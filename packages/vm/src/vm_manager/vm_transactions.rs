use std::{collections::HashMap, sync::Arc};

use cosmwasm_std::{Addr, Binary, BlockInfo, Coin, ContractInfo, CosmosMsg, Empty, Env, IbcAcknowledgement, IbcMsg, IbcOrder, IbcTimeout, IbcTimeoutBlock, Reply, ReplyOn, SubMsg, SubMsgResponse, SubMsgResult, Timestamp, TransactionInfo, WasmMsg};
use serde::{Deserialize, Serialize};

use prost::Message;
use serde_json::de::Read;
use lazy_static::lazy_static;

use crate::{call_execute, call_instantiate, call_migrate, call_reply, symb_exec::{ProfileEvaluator, ProfileGenerator}, testing::{mock_info, ConcurrentStorage, StorageWrapper}, BackendApi, Instance, Querier, ReadWrite, VMManager};

use super::{sc_storage::{CodeId, ConcurrentTimer}, ConcurrentSchedule, EnvironmentContext, ReplayLogs, ScAddr, TxId};

// 
// Francisco Rola
// 

lazy_static! {
    // A static timer that tracks the total elapsed time.
    static ref TIMER: ConcurrentTimer = ConcurrentTimer::new();
}

pub fn print_vm_transaction_times(n_threads: u16) {
    println!("VM_TRANSACTIONS ---");
    println!("execution_timer: ~{:?} per thread", TIMER.get_value() / (n_threads as u32));
    println!("---");
}


#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct SerializableTransaction {
    pub transaction: TransactionEnum,
    pub log_instantiate: HashMap<CodeId, Vec<String>>,
    pub log_execute: Vec<String>,
    pub log_reply: Vec<String>,
    pub log_migrate: HashMap<String, Vec<CodeId>>,
    pub rws: TransactionRWS,
}

impl SerializableTransaction {
    pub fn without_logs_or_rws(tx_enum: TransactionEnum) -> Self {
        SerializableTransaction {
            transaction: tx_enum,
            log_execute: vec![],
            log_instantiate: HashMap::new(),
            log_migrate: HashMap::new(),
            log_reply: vec![],
            rws: TransactionRWS::default(),
        }
    }

    pub fn with_log_instantiate(tx_enum: TransactionEnum, log_instantiate: HashMap<CodeId, Vec<String>>) -> Self {
        SerializableTransaction {
            transaction: tx_enum,
            log_execute: vec![],
            log_instantiate,
            log_migrate: HashMap::new(),
            log_reply: vec![],
            rws: TransactionRWS::default(),
        }
    }

    pub fn with_log_execute(tx_enum: TransactionEnum, log_execute: Vec<String>) -> Self {
        SerializableTransaction {
            transaction: tx_enum,
            log_execute,
            log_instantiate: HashMap::new(),
            log_migrate: HashMap::new(),
            log_reply: vec![],
            rws: TransactionRWS::default(),
        }
    }
}

// Transaction structures
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(tag = "type")]
pub enum TransactionEnum {
    Instantiate(InstantiateTx),
    Execute(ExecuteTx),
    Reply(ReplyTx),
    Migrate(MigrateTx),
    StoreCode(StoreCodeTx),
    ChannelOpenInit(ChannelOpenInitTx),
    ChannelOpenTry(ChannelOpenTryTx),
    ChannelOpenAck(ChannelOpenAckTx),
    ChannelOpenConfirm(ChannelOpenConfirmTx),
    RecvPacket(RecvPacketTx),
    Timeout(TimeoutTx),
    Ack(AckTx),
    NotSupported(NotSupportedTx),
    Abort(AbortTx),
}

/// Define logs that hold relevant information of nested invocations
/// Each log is only associated with its corresponding type of transaction.
/// Meaning if the top-level transaction is an Instantiate, and it has an entry in the log_execute,
/// this means the Instantiate will call a nested executed, which will need the information from that log
/// to be executed.
pub struct ReplayLogsMutRef<'a> {
    pub log_execute: &'a mut Vec<String>,
    pub log_instantiate: &'a mut HashMap<u32, Vec<String>>,
    pub log_reply: &'a mut Vec<String>,
    pub log_migrate: &'a mut HashMap<String, Vec<CodeId>>
}

impl<'a> ReplayLogsMutRef<'a> {
    pub fn from_replay_logs(replay_logs: &'a mut ReplayLogs) -> Self {
        ReplayLogsMutRef {
            log_execute: &mut replay_logs.log_execute,
            log_instantiate: &mut replay_logs.log_instantiate,
            log_reply: &mut replay_logs.log_reply,
            log_migrate: &mut replay_logs.log_migrate,
        }
    }
}

/// Holds the context to create a VM instance, and possibly also a reference to a VM instance
/// Only instantiates will need the context, but may also need the instance reference, if the instantiate
/// is a nested. Then it will create N vms with the given context, but will still execute in the passed VM,
/// which is part of the caller's context
pub struct VMResource<'a, A, S, W, Q, E> 
where
    A: BackendApi                           + 'static + Sync + Send, 
    S: ConcurrentStorage                    + 'static + Sync + Send, 
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Sync + Send,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Sync + Send,
{
    pub instance: Option<* mut Instance<A, W, Q>>,
    pub environment: EnvironmentContext<'a, A, S, W, Q, E>
}

impl<'a, A, S, W, Q, E> VMResource<'a, A, S, W, Q, E> 
where
    A: BackendApi                           + 'static + Sync + Send, 
    S: ConcurrentStorage                    + 'static + Sync + Send, 
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Sync + Send,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Sync + Send,
{
    fn set_instance(&mut self, instance: * mut Instance<A, W, Q>) {
        self.instance = Some(instance);
    }

    fn clear_instance(&mut self) {
        self.instance = None;
    }
}

/// Generic process method all transaction types must implement
pub trait Transaction<A, S, W, Q, E>
where
    A: BackendApi                           + 'static + Sync + Send, 
    S: ConcurrentStorage                    + 'static + Sync + Send, 
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Sync + Send,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Sync + Send,
{
    fn process(&mut self, vm_resource: &mut VMResource<A, S, W, Q, E>, execution_logs: &mut ReplayLogsMutRef) -> std::io::Result<String>;
}

/// Delegates the execution to the correct tx type
impl<A, S, W, Q, E> Transaction<A, S, W, Q, E> for TransactionEnum
where
    A: BackendApi                           + 'static + Sync + Send, 
    S: ConcurrentStorage                    + 'static + Sync + Send, 
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Sync + Send,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Sync + Send,
{
    fn process(&mut self, vm_resource: &mut VMResource<A, S, W, Q, E>, execution_logs: &mut ReplayLogsMutRef) -> std::io::Result<String> {
        let tx: &mut dyn Transaction<A, S, W, Q, E> = match self {
            TransactionEnum::Instantiate(tx) => tx,
            TransactionEnum::Execute(tx) => tx,
            // TransactionEnum::Reply(tx) |
            // TransactionEnum::Migrate(tx) |
            // TransactionEnum::StoreCode(tx) |
            // TransactionEnum::ChannelOpenTry(tx) |
            // TransactionEnum::ChannelOpenAck(tx) |
            // TransactionEnum::ChannelOpenConfirm(tx) |
            // TransactionEnum::ChannelOpenInit(tx) |
            // TransactionEnum::RecvPacket(tx) |
            // TransactionEnum::Timeout(tx) |
            // TransactionEnum::Ack(tx) |
            // TransactionEnum::NotSupported(tx) |
            // TransactionEnum::Abort(tx) 
            _ => todo!()
        };

        tx.process(vm_resource, execution_logs)
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct ReplyStruct {
    reply_on: bool,
    reply_id: u64,
    reply_payload: Binary,
    reply_address: String,
}
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct InstantiateTx {
    pub hash: String,
    pub sender: String,
    pub label: String,
    pub funds: Vec<Coin>,
    pub msg: Vec<u8>,
    pub code_id: u32,
    pub reply: Option<ReplyStruct>,
}
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct ExecuteTx {
    pub hash: String,
    pub sender: String,
    pub funds: Vec<Coin>,
    pub msg: Vec<u8>,
    pub contract_addr: String,
    pub reply: Option<ReplyStruct>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct ReplyTx {
    pub msg: Reply,
    pub contract_addr: String,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct MigrateTx {
    pub hash: String,
    pub sender: String,
    pub code_id: CodeId,
    pub msg: Vec<u8>,
    pub contract_addr: String,
    pub reply: Option<ReplyStruct>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct StoreCodeTx {
    pub hash: String,
    pub wasm: Box<[u8]>,
    pub log_store_code: i32,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct ChannelOpenInitTx {
    pub hash: String,
    pub ordering: IbcOrder,
    pub port_id: String,
    pub channel_id: String,
    pub counterparty_port_id: String,
    pub counterparty_channel_id: String,
    pub connection_id: String,
    pub version: String,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct ChannelOpenTryTx {
    pub hash: String,
    pub ordering: IbcOrder,
    pub port_id: String,
    pub channel_id: String,
    pub counterparty_port_id: String,
    pub counterparty_channel_id: String,
    pub connection_id: String,
    pub version: String,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct ChannelOpenAckTx {
    pub hash: String,
    pub port_id: String,
    pub channel_id: String,
    pub counterparty_port_id: String,
    pub counterparty_channel_id: String,
    pub connection_id: String,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct ChannelOpenConfirmTx {
    pub hash: String,
    pub port_id: String,
    pub channel_id: String,
    pub counterparty_port_id: String,
    pub counterparty_channel_id: String,
    pub connection_id: String,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct RecvPacketTx {
    pub hash: String,
    pub relayer: Addr,
    pub data: Binary,
    pub port_id: String,
    pub channel_id: String,
    pub counterparty_port_id: String,
    pub counterparty_channel_id: String,
    pub sequence: u64,
    pub timeout: IbcTimeout
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct TimeoutTx {
    pub hash: String,
    pub relayer: Addr,
    pub data: Binary,
    pub port_id: String,
    pub channel_id: String,
    pub counterparty_port_id: String,
    pub counterparty_channel_id: String,
    pub sequence: u64,
    pub timeout: IbcTimeout
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct AckTx {
    pub hash: String,
    pub acknowledgement: IbcAcknowledgement,
    pub relayer: Addr,
    pub data: Binary,
    pub port_id: String,
    pub channel_id: String,
    pub counterparty_port_id: String,
    pub counterparty_channel_id: String,
    pub sequence: u64,
    pub timeout: IbcTimeout
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct NotSupportedTx {
    pub hash: String,
    pub tx_type: String,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct AbortTx {
    pub hash: String,
}

#[derive(Clone, PartialEq, Message)]
struct MsgInstantiateContractResponse {
    #[prost(string, tag = "1")]
    pub contract_address: String,
    #[prost(bytes, tag = "2")]
    pub data: Vec<u8>,
}

#[derive(Clone, PartialEq, Message)]
struct MsgExecuteContractResponse {
    #[prost(bytes, tag = "1")]
    pub data: Vec<u8>,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, Default)]
pub struct TransactionRWS {
    read_set: HashMap<String, Vec<String>>,
    write_set: HashMap<String, Vec<String>>,
}

#[derive(Serialize, Deserialize)]
struct WasmLog {
    log_execute: Vec<String>,
    log_instantiate: HashMap<i32, Vec<String>>,
    log_reply: Vec<String>,
    log_migrate: HashMap<String, Vec<i32>>,
}

#[derive(Serialize, Deserialize)]
struct WasmFields {
    tx_hash: Option<String>,
    tx_type: Option<String>,
    sender: Option<String>,
    label: Option<String>,
    funds: Option<Vec<Coin>>,
    msg: Option<Vec<u8>>,
    contract: Option<String>,
    code_id: Option<i32>,
}

#[derive(Serialize, Deserialize)]
struct IbcFields {
    tx_hash: Option<String>,
    tx_type: Option<String>,
    ordering: Option<IbcOrder>,
    acknowledgement: Option<IbcAcknowledgement>,
    relayer: Option<Addr>,
    port_id: Option<String>,
    channel_id: Option<String>,
    cp_port_id: Option<String>,
    cp_channel_id: Option<String>,
    connection_id: Option<String>,
    version: Option<String>,
    packet_data: Option<Binary>,
    sequence: Option<u64>,
    timeout_block: Option<IbcTimeoutBlock>,
    timeout_timestamp: Option<Timestamp>,
}

fn create_neutron_env(contract_addr: String) -> Env {
    // Create an env variable,the only field that matters in our context is contract_address

    let env = Env {
        block: BlockInfo {
            height: 12_345,
            time: Timestamp::from_nanos(1_691_797_419_879_305_533),
            chain_id: "neutron-1".to_string(),
        },
        transaction: Some(TransactionInfo { index: 3 }),
        contract: ContractInfo {
            address: Addr::unchecked(&contract_addr.clone()),
        },
    };

    env
}


/// If an instance is passed, then execute the instance_work on that instance. Else,
/// fetch a free VM from the VMManager and execute the instance_work using that instance
fn execute_vm<A, S, W, Q, E, F>(
    vm_resource: &mut VMResource<A, S, W, Q, E>, 
    contract_address: &ScAddr, 
    instance_work: F) -> std::io::Result<String>
where
    A: BackendApi                           + 'static + Sync + Send, 
    S: ConcurrentStorage                    + 'static + Sync + Send, 
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Sync + Send,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Sync + Send,
    F: FnOnce(&mut Instance<A, W, Q>, &mut VMResource<A, S, W, Q, E>) -> std::io::Result<String>
{
    // if instantiate is nested within a higher-level caller -> just use the caller's instance
    if let Some(instance) = vm_resource.instance {
        let instance: &mut Instance<A, W, Q> = unsafe { &mut *instance };
        instance_work(instance, vm_resource)
    }
    // grab one free instance from the newly instanciated VMs for the new contract address & use it
    else {
        VMManager::execute_vm(vm_resource.environment.mut_clone(), contract_address, |instance| instance_work(instance, vm_resource))
    }
}


impl<A, S, W, Q, E> Transaction<A, S, W, Q, E> for InstantiateTx
where
    A: BackendApi                           + 'static + Sync + Send, 
    S: ConcurrentStorage                    + 'static + Sync + Send, 
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Sync + Send,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Sync + Send,
{

    fn process(&mut self, vm_resource: &mut VMResource<A, S, W, Q, E>, replay_logs: &mut ReplayLogsMutRef) -> std::io::Result<String> {
        // Grab the contract address resulting from the instantiate, present in the log
        let contract_addr = replay_logs.log_instantiate
            .get(&self.code_id)
            .and_then(|vec| vec.get(0))
            .expect("Contract address not found in instantiate log")
            .to_string();


        VMManager::compile_instantiate_vm(&vm_resource.environment, &contract_addr, self.code_id);

        // Convert the msg to a byte vector
        let msg: &[u8] = self.msg.as_slice();
        let info = mock_info(self.sender.as_str(), &self.funds);

        // auxiliary closure that, given an instance, does all needed work with that instance. This may involve
        // executing nested calls within that instance
        let mut instance_work = |instance: &mut Instance<A, W, Q>, vm_resource: &mut VMResource<A, S, W, Q, E>| {
            vm_resource.set_instance(instance);

            let contract_result =
            call_instantiate::<_, _, _, Empty>(instance, &create_neutron_env(contract_addr.clone()), &info, msg).unwrap();

            // println!("INSTANTIATE RESULT: {:?}", contract_result);

            // Remove instantiate of current transaction from the instantiate log as it has been performed
            if let Some(vec) = replay_logs.log_instantiate.get_mut(&self.code_id) {
                //println!("Removing element from vec: {}", &self.code_id);
                vec.remove(0);
                if vec.is_empty() {
                    //println!("Removing key: {}", &self.code_id);
                    replay_logs.log_instantiate.remove(&self.code_id);
                }
            }
            //println!("Leftover log: {}", log_instantiate.len());
    
            // Handle the result and look for potential nested transactions
            let res = contract_result.unwrap();

            if !res.messages.is_empty() {
                handle_result_json(
                    res.messages.clone(), 
                    vm_resource,
                    replay_logs, 
                    contract_addr.clone()
                );
            }
    
            // Check if there is a reply to be sent
            match &mut self.reply {
                Some(reply_struct) => {
                    if reply_struct.reply_on {
    
                        // Create an instantiate reply
                        let instantiate_reply = MsgInstantiateContractResponse {
                            contract_address: contract_addr.clone(),
                            data: vec![],
                        };
    
                        // Encode the instantiate reply
                        let mut encoded_instantiate_reply = Vec::<u8>::with_capacity(instantiate_reply.encoded_len());
                        instantiate_reply
                            .encode(&mut encoded_instantiate_reply)
                            .unwrap();
    
                        // Build a reply msg
                        let reply_msg = Reply {
                            id: reply_struct.reply_id,
                            payload: reply_struct.reply_payload.clone(),
                            gas_used: 1,
                            result: SubMsgResult::Ok(SubMsgResponse {
                                events: vec![],
                                data: Some(encoded_instantiate_reply.into()),
                                msg_responses: vec![],
                            }),
                        };
    
                        // Build a reply tx
                        let mut reply_tx = ReplyTx {
                            msg: reply_msg,
                            contract_addr: reply_struct.reply_address.clone(),
                        };
                        reply_tx.process(vm_resource, replay_logs);
                    }
                }
                None => {
                    // Do nothing in a scenario where there is no reply
                }
            };

            vm_resource.clear_instance();

            Ok(format!("{:?}", res))
        };

        execute_vm(vm_resource, &contract_addr, instance_work)

    }
}


impl<A, S, W, Q, E> Transaction<A, S, W, Q, E> for ExecuteTx  
where
    A: BackendApi                           + 'static + Sync + Send, 
    S: ConcurrentStorage                    + 'static + Sync + Send, 
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Sync + Send,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Sync + Send,

{
    fn process(&mut self, vm_resource: &mut VMResource<A, S, W, Q, E>, replay_logs: &mut ReplayLogsMutRef) -> std::io::Result<String> {

        // Grab sender and funds, create info object for transaction execution
        let info = mock_info(self.sender.as_str(), &self.funds);

        // Convert the msg to a byte vector
        let msg: &[u8] = self.msg.as_slice();


        let instance_work = |instance: &mut Instance<A, W, Q>, vm_resource: &mut VMResource<A, S, W, Q, E>| {
            vm_resource.set_instance(instance);

            let timer = TIMER.create_scoped_timer();
            let contract_result =
                call_execute::<_, _, _, Empty>(instance, &create_neutron_env(self.contract_addr.clone()), &info, msg).unwrap();
            TIMER.add_scoped_timer(timer);
            
            // Remove execute  of current transaction from the execute log as it has been performed
            replay_logs.log_execute.remove(replay_logs.log_execute.iter().position(|x| x == &self.contract_addr.clone()).expect("Failed to remove address from execute_log"));

            // Grab the result and handle it, potentially dealing with sub messages
            let res = contract_result.unwrap();

            if !res.messages.is_empty() {
                handle_result_json(
                    res.messages.clone(),
                    vm_resource,
                    replay_logs, 
                    self.contract_addr.clone()
                );
            }

            // Check if there is a reply to be sent
            match &mut self.reply {
                Some(reply_struct) => {
                    if reply_struct.reply_on {

                        // Create an execute reply
                        let execute_reply = MsgExecuteContractResponse {
                            data: vec![],
                        };

                        // Encode the execute reply
                        let mut encoded_execute_reply = Vec::<u8>::with_capacity(execute_reply.encoded_len());
                        execute_reply
                            .encode(&mut encoded_execute_reply)
                            .unwrap();

                        // Build a reply msg
                        let reply_msg = Reply {
                            id: reply_struct.reply_id,
                            payload: reply_struct.reply_payload.clone(),
                            gas_used: 1,
                            result: SubMsgResult::Ok(SubMsgResponse {
                                events: vec![],
                                data: Some(encoded_execute_reply.into()),
                                msg_responses: vec![],
                            }),
                        };

                        // Build a reply tx
                        let mut reply_tx = ReplyTx {
                            msg: reply_msg,
                            contract_addr: reply_struct.reply_address.clone(),
                        };

                        reply_tx.process(vm_resource, replay_logs);
                    }
                }
                None => {
                    // Do nothing in a scenario where there is no reply
                }
            };

            vm_resource.clear_instance();

            Ok(format!("{:?}", res))
        };

        let res = execute_vm(vm_resource, &self.contract_addr, instance_work);
        res      
    }
}



impl<A, S, W, Q, E> Transaction<A, S, W, Q, E> for ReplyTx 
where
    A: BackendApi                           + 'static + Sync + Send, 
    S: ConcurrentStorage                    + 'static + Sync + Send, 
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Sync + Send,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Sync + Send,
{
    fn process(&mut self, vm_resource: &mut VMResource<A, S, W, Q, E>, replay_logs: &mut ReplayLogsMutRef) -> std::io::Result<String> {

        let instance_work = |instance: &mut Instance<A, W, Q>, vm_resource: &mut VMResource<A, S, W, Q, E>| {
            vm_resource.set_instance(instance);

            // Get a VM to run the transaction, from the reply body and run it
            let contract_result =
                call_reply::<_, _, _, Empty>(instance, &create_neutron_env(self.contract_addr.clone()), &self.msg).unwrap();
            println!("REPLY RESULT: {:?}", contract_result);

            // A reply cannot be invoked as an answer to another reply so no need to check reply field in reply_tx


            // Remove current transaction from the reply log as it has been performed
            replay_logs.log_reply.remove(replay_logs.log_reply.iter().position(|x| x == &self.contract_addr.clone()).expect("Failed to remove address from reply_log"));

            // A reply can trigger a nested execute, potentially also instantiate
            let res = contract_result.unwrap();

            if !res.messages.is_empty() {
                handle_result_json(
                    res.messages.clone(), 
                    vm_resource,
                    replay_logs, 
                    self.contract_addr.clone()
                );
            }

            vm_resource.clear_instance();

            Ok(format!("{:?}", res))
        };

        execute_vm(vm_resource, &self.contract_addr, instance_work)
    }
}


impl<A, S, W, Q, E> Transaction<A, S, W, Q, E> for MigrateTx 
where
    A: BackendApi                           + 'static + Sync + Send, 
    S: ConcurrentStorage                    + 'static + Sync + Send, 
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Sync + Send,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Sync + Send,
{
    fn process(&mut self, vm_resource: &mut VMResource<A, S, W, Q, E>, replay_logs: &mut ReplayLogsMutRef) -> std::io::Result<String> {

        println!("Migrating contract: {}", self.contract_addr.clone());

        // Convert the msg to a byte vector
        let msg: &[u8] = self.msg.as_slice();

        let instance_work = |instance: &mut Instance<A, W, Q>| {
            vm_resource.set_instance(instance);
        
            // Run execute transaction
            let contract_result =
                call_migrate::<_, _, _, Empty>(instance, &create_neutron_env(self.contract_addr.clone()), msg).unwrap();
            println!("MIGRATE RESULT: {:?}", contract_result);


            // Remove migrate of current transaction from the migrate log as it has been performed
            if let Some(vec) = replay_logs.log_migrate.get_mut(&self.contract_addr) {
                //println!("Removing element from vec: {}", &self.contract_addr);
                vec.remove(vec.iter().position(|x| x == &self.code_id.clone()).expect("Failed to remove <contract,code_id> from migrate_log"));
                if vec.is_empty() {
                    //println!("Removing key: {}", &self.code_id);
                    replay_logs.log_migrate.remove(&self.contract_addr);
                }
            }
            

            // Grab the result and handle it, potentially dealing with sub messages
            let res = contract_result.unwrap();

            if !res.messages.is_empty() {
                handle_result_json(res.messages.clone(), vm_resource, replay_logs, self.contract_addr.clone());
            }

            // Check if there is a reply to be sent
            match &mut self.reply {
                Some(reply_struct) => {
                    if reply_struct.reply_on {

                        // Create an execute reply
                        let execute_reply = MsgExecuteContractResponse {
                            data: vec![],
                        };

                        // Encode the execute reply
                        let mut encoded_execute_reply = Vec::<u8>::with_capacity(execute_reply.encoded_len());
                        execute_reply
                            .encode(&mut encoded_execute_reply)
                            .unwrap();

                        // Build a reply msg
                        let reply_msg = Reply {
                            id: reply_struct.reply_id,
                            payload: reply_struct.reply_payload.clone(),
                            gas_used: 1,
                            result: SubMsgResult::Ok(SubMsgResponse {
                                events: vec![],
                                data: Some(encoded_execute_reply.into()),
                                msg_responses: vec![],
                            }),
                        };

                        // Build a reply tx
                        let mut reply_tx = ReplyTx {
                            msg: reply_msg,
                            contract_addr: reply_struct.reply_address.clone(),
                        };

                        reply_tx.process(vm_resource, replay_logs);
                    }
                }
                None => {
                    // Do nothing in a scenario where there is no reply
                }
            }

            vm_resource.clear_instance();
            todo!()
            // Ok(format!("{:?}", res))
        };

        todo!()
        // VMManager::migrate_vm(vm_resource.environment, &self.contract_addr, self.code_id, instance_work)
    }
}



/// Handles the nested sub messages vector
fn handle_result_json<A, S, W, Q, E>(messages: Vec<SubMsg>, vm_resource: &mut VMResource<A, S, W, Q, E>, replay_logs: &mut ReplayLogsMutRef, sender: String) 
where
    A: BackendApi                           + 'static + Sync + Send, 
    S: ConcurrentStorage                    + 'static + Sync + Send, 
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Sync + Send,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Sync + Send,
{

    for sub_msg in messages {

        // Check whether replyOn was set, if yes prepare a reply structure to include in sub-tx
        let reply_option = {
            if sub_msg.reply_on == ReplyOn::Always || sub_msg.reply_on == ReplyOn::Success {
                Some(ReplyStruct {
                    reply_on: true,
                    reply_id: sub_msg.id,
                    reply_payload: sub_msg.payload,
                    reply_address: sender.clone(),
                })
            } else {
                None
            }
        };

        let nested_msg = sub_msg.msg;

        match nested_msg {
            CosmosMsg::Wasm(wasm_msg) => {
                match wasm_msg {
                    WasmMsg::Instantiate { admin, code_id, msg, funds, label } => {

                        let code_id: u32 = code_id.try_into().expect("Conversion not possible, value too large");

                        let mut instantiate_tx = InstantiateTx {
                            hash: "nested_tx".to_string(),
                            sender: sender.clone(),
                            msg: msg.as_slice().to_vec(),
                            funds: funds.clone(),
                            reply: reply_option,
                            label: label,
                            code_id: code_id,
                        };
                        // Run the nested migrate transaction
                        instantiate_tx.process(vm_resource, replay_logs);
                    }

                    WasmMsg::Execute { contract_addr, msg, funds } => {

                        let mut execute_tx = ExecuteTx {
                            hash: "nested_tx".to_string(),
                            sender: sender.clone(),
                            msg: msg.as_slice().to_vec(),
                            funds: funds.clone(),
                            contract_addr: contract_addr,
                            reply: reply_option,
                        };
                        // Run the nested migrate transaction
                        execute_tx.process(vm_resource, replay_logs);
                    }

                    WasmMsg::Migrate { contract_addr, new_code_id, msg } => {

                        let code_id: u32 = new_code_id.try_into().expect("Conversion not possible, value too large");

                        //println!("addr: {}", contract_addr.clone());
                        //println!("code_id: {}", code_id.clone());
                        //println!("msg: {}", msg.to_base64());

                        let mut migrate_tx = MigrateTx {
                            hash: "nested_tx".to_string(),
                            sender: sender.clone(),
                            code_id: code_id,
                            msg: msg.as_slice().to_vec(),
                            contract_addr: contract_addr,
                            reply: reply_option,
                        };
                        // Run the nested migrate transaction
                        migrate_tx.process(vm_resource, replay_logs);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}