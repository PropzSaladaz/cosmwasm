use std::{cmp::Ordering, collections::{HashMap, HashSet}, sync::{Arc, Mutex, RwLock}, thread};

use cosmwasm_std::{Api, CustomQuery, Empty, QuerierWrapper};
use wasmer::Store;

use crate::{
    backend::ConcurrentBackend, call_execute, call_instantiate, call_query, internals::instance_from_module, 
    symb_exec::{Commutativity, Key, ReadWrite, SEStatus, StorageDependency, TxRWS}, 
    testing::{mock_env, mock_info, ConcurrentStorage, MockApi, MockQuerier, MockConcurrentStorage, MockStorageWrapper}, 
    vm_manager::ContractRWS, wasm_backend::{compile, make_compiling_engine, make_runtime_engine}, 
    BackendApi, ConcurrentSchedule, InstanceOptions, Querier, SCProfile, Size, Storage
};

use super::sc_storage::{PersistentBackend, SCManager};

const DEFAULT_MEMORY_LIMIT: Size = Size::mebi(64);
const HIGH_GAS_LIMIT: u64 = 20_000_000_000_000_000; // ~20s, allows many calls on one instance


enum VMCall {
    Execute,
    Query,
}

#[derive(Debug, PartialEq, Clone)]
pub enum VMMessage {
    Instantiation {
        message: Vec<u8>,
        contract_code_id: u128,
    },
    Invocation {
        message: Vec<u8>,
        entry_point: InstantiatedEntryPoint,
        contract_address: String,
        code_id: u128,
    },
}

impl VMMessage {
    fn default() -> VMMessage {
        VMMessage::Invocation {
            message: vec![],
            entry_point: InstantiatedEntryPoint::Execute,
            contract_address: String::from(""),
            code_id: 0,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum InstantiatedEntryPoint {
    Execute,
    Query,
    Reply
}


type Counter = i32;
pub type Block = Vec<VMMessage>;

/// mapping (code_id, nth_instantiation) => address
pub type AddressMapper = dyn Fn(u128, u128) -> String + Sync + Send;
pub type BackendBuilder<A, S, Q> = dyn Fn(Arc<S>) -> PersistentBackend<A, S, Q> + Send + Sync;

/// Stateful manager used to instantiate VMs for contract execution,
/// passing them a reference to its corresponding persistent storage
pub struct VMManager<A, S, Q>
where
    A: BackendApi + 'static + Send + Sync,
    S: ConcurrentStorage + 'static + Send + Sync,
    Q: Querier + 'static + Send + Sync,
{
    state_manager: Arc<RwLock<SCManager<A, S, Q>>>,

    /// will be computed when blockchain is replayed, & when we instantiate contracts, etc we
    /// will use the addresses from the replay
    address_mapper: Arc<AddressMapper>,
    
    backend_builder: Arc<BackendBuilder<A, S, Q>>, 
}

struct ThreadExecutionContext<A, S, Q>
where
    A: BackendApi + 'static + Sync + Send,
    S: ConcurrentStorage + 'static + Sync + Send,
    Q: Querier + 'static + Sync + Send, 
{
    state_manager:  Arc<RwLock<SCManager<A, S, Q>>>,
    backend_builder: Arc<BackendBuilder<A, S, Q>>,
    address_mapper: Arc<AddressMapper>,
}


/// This is a read-only version of depsMut -> we won't change anything
/// in it when parsing the RWS, thus storage can be a immutable reference
pub struct DepsMut<'a, C: CustomQuery = Empty> {
    pub storage: &'a dyn cosmwasm_std::Storage,
    pub api: &'a dyn Api,
    pub querier: QuerierWrapper<'a, C>,
}


/// Used to keep a connection between a RWS and a message that originated that RWS.
/// This is first used when fetching the list of RWS given a block of messages, and then is
/// passed to the execution.
#[derive(Debug)]
pub struct RWSContext {
    pub rws: TxRWS,
    pub address: String, 
    pub tx_message: Option<VMMessage>,
    pub tx_block_id: u16,
}


impl PartialEq for RWSContext {
    fn eq(&self, other: &Self) -> bool {
        self.rws == other.rws && 
        self.address == other.address &&
        match (&self.tx_message, &other.tx_message) {
            (Some(a), Some(b)) => a == b,
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        }
    }
}


impl<A, S, Q> VMManager<A, S, Q> 
where
    A: BackendApi + Sync + Send, 
    S: ConcurrentStorage + Sync + Send, 
    Q: Querier + Sync + Send
{

    pub fn new(state_manager: Arc<RwLock<SCManager<A, S, Q>>>, address_mapper: Arc<AddressMapper>,
        backend_builder: Arc<BackendBuilder<A, S, Q>>) -> Self
    {
        VMManager {
            state_manager,
            address_mapper,
            backend_builder
        }
    }

    /// Given a block of messages, fetch the RWS for each individual tx - this is done using information from the
    /// contract inputs and the already built SE profile when the SC was installed.
    /// 
    /// Then build a schedule from the RWS, marking all the dependencies across operations.
    /// Execute in arallel respecting the dependencies across operations.
    /// 
    /// At the end of execution, persist the final state to storage.
    pub fn handle_block(&mut self, block: Block) -> std::io::Result<Vec<String>> {
        let mut rws: Vec<RWSContext> = self.get_rws(block);
        
        let mut schedule = ConcurrentSchedule::new();
        schedule.build_from_rws(&mut rws);

        let resps = self.execute_block(rws, schedule).unwrap();

        Ok(resps)
    }

    /// Get the RWS given an input message for some contract.
    /// Fetches the SE profile, parses it & gets the final RWS in form of keys as bytes
    /// It returns a vec where each item contains the contract address as well as all the keys
    /// it will touch
    /// The return vector places all COMPLETE & INDEPENDENT txs first, and only after all the INCOMPLETE or DEPENDENT txs
    fn get_rws(&self, block: Block) -> Vec<RWSContext> {
        let mut rws_complete_and_independent = vec![];
        let mut rws_incomplete_or_dependent = vec![];
        for msg in block.into_iter() {
            let rws = match msg {
                VMMessage::Instantiation { 
                    message: _, 
                    contract_code_id: _,
                } => RWSContext {
                        // rws goes empty - there are no conflicts within instantiates for the same contract storage since instantiates
                        // generate a brand new storage
                        rws: TxRWS { storage_dependency: StorageDependency::Independent, profile_status: SEStatus::Complete, rws: vec![]},
                        address: String::from(""),
                        tx_message: Some(msg),
                        tx_block_id: 0,
                 },

                VMMessage::Invocation { 
                    ref message, // ref is used not to move this field. Else, we would not be able to move it into the Some(msg) below
                    ref entry_point,
                    ref contract_address, 
                    ref code_id
                } => {
                    let profile = self.state_manager.read().unwrap().get_profile(*code_id);
                    match &self.state_manager.read().unwrap().get_instance_data(&contract_address) {
                        Some(sc_instance) => {
                            // Build mock depsMut
                            let storage = Arc::clone(&sc_instance.state.storage);
                            let mut context = VMManager::<A, S, Q>::get_rws_for_invocation(
                                                        &entry_point, profile, message.as_slice(), &contract_address, storage);
                            context.tx_message = Some(msg);
                            context
                        }
                        // If invocation on a contract that wasn't yet instantiated
                        None => {
                            // creates empty storage for such cases
                            let mut context = VMManager::<A, S, Q>::get_rws_for_invocation(&entry_point, profile, message.as_slice(), 
                                &contract_address, Arc::new(S::new()));
                            context.tx_message = Some(msg);
                            context
                        }

                    }
                }
            };

            if (rws.rws.profile_status == SEStatus::Complete) && (rws.rws.storage_dependency == StorageDependency::Independent) {
                rws_complete_and_independent.push(rws);
            }
            else {
                rws_incomplete_or_dependent.push(rws);
            }
        };
        // append incomplete || dependent RWSs at the end
        rws_complete_and_independent.append(&mut rws_incomplete_or_dependent);
        // set tx id as the index in the block
        for (idx, el) in rws_complete_and_independent.iter_mut().enumerate() {
            el.tx_block_id = idx as u16;
        }

        rws_complete_and_independent
    }

    fn get_rws_for_invocation(entry_point: &InstantiatedEntryPoint, profile: Arc<SCProfile>, message: &[u8],
        contract_address: &String, storage: Arc<S>) -> RWSContext
    {
        let querier = cosmwasm_std::testing::MockQuerier::default();
        let mut_deps = DepsMut { 
            storage: &*storage,
            api: &cosmwasm_std::testing::MockApi::default(), 
            querier: cosmwasm_std::QuerierWrapper::new( &querier)
        };
        match entry_point {
            InstantiatedEntryPoint::Execute => 
                RWSContext {
                    rws: profile.get_rws_execute(&mut_deps, &mock_env(), &mock_info("", &[]), message),
                    address: contract_address.clone(),
                    tx_message: None, // will be set by calling function
                    tx_block_id: 0,   // will be set by calling function
                },
            InstantiatedEntryPoint::Query   => {
                RWSContext {
                    rws: profile.get_rws_query(&mut_deps, &mock_env(), message),
                    address: contract_address.clone(),
                    tx_message: None, // will be set by calling function
                    tx_block_id: 0,   // will be set by calling function
                }
            },
            InstantiatedEntryPoint::Reply => todo!(),
        }
    }

    fn get_execution_context(&self) -> ThreadExecutionContext<A, S, Q> {
        ThreadExecutionContext {
            state_manager: Arc::clone(&self.state_manager),
            backend_builder: Arc::clone(&self.backend_builder),
            address_mapper: Arc::clone(&self.address_mapper)
        }
    }

    fn execute_block(&mut self, rws: Vec<RWSContext>, schedule: ConcurrentSchedule) -> std::io::Result<Vec<String>> {
        const N_THREADS: u16 = 1;
        let mut handles = vec![];
        let resps = Arc::new(Mutex::new(vec![]));
        let schedule = Arc::new(schedule);
        let rws = Arc::new(rws);
        let thread_exec_ctx = Arc::new(VMManager::get_execution_context(&self));

        // execute each message
        for i in 0..N_THREADS {
            let schedule_ref = Arc::clone(&schedule);
            let resps_ref = Arc::clone(&resps);
            let rws_ref = Arc::clone(&rws);
            let thread_exec_ctx_ref = Arc::clone(&thread_exec_ctx);

            let handle = thread::spawn(move || {
                loop {
                    println!("Thread: {:?} waiting for message to execute", i);
                    if let Some(tx_id) = &schedule_ref.get_next_message_to_execute() {
                        println!("Thread: {:?} executing message: {:?}", i, tx_id);
                        let message = &rws_ref[*tx_id as usize];
                        // TODO - below clone should be optimized - no need.. we can pass a reference, or just return the same arc from the method
                        let resp = VMManager::execute_message(Arc::clone(&schedule_ref), &*thread_exec_ctx_ref, message);
                        schedule_ref.on_tx_finish(*tx_id);
                        resps_ref.lock().unwrap().push(resp);
                    }
                    else {
                        println!("Thread {:?} finished executing", i); 
                        break; 
                    }
                }
            });

            handles.push(handle);
        }

        // wait for all threads
        for handle in handles {
            handle.join().unwrap();
        }

        self.persist_schedule(schedule);

        // return the response vector contents
        let mut guard = resps.lock().unwrap();
        Ok(std::mem::take(&mut *guard))
    }

    fn persist_schedule(&self, concurrent_schedule: Arc<ConcurrentSchedule>) {
        let sc_storage_manager_lock = self.state_manager.read().unwrap();
        concurrent_schedule.persist_schedule(&*sc_storage_manager_lock);
    }

    fn execute_message(schedule: Arc<ConcurrentSchedule>, thread_exec_context: &ThreadExecutionContext<A, S, Q>, msg: &RWSContext) -> String {
        // TODO - try passing a reference here -> we need to change later on the backend and mocksStorage to handle references instead of
        // Vec. Cloning the entire RWS is very innefficient here..
        let rws = msg.rws.rws.clone();

        match &msg.tx_message {
            Some(VMMessage::Instantiation { 
                message, 
                contract_code_id,
            }) => VMManager::compile_instantiate_vm(msg.tx_block_id, schedule, &thread_exec_context, *contract_code_id, message.as_slice(), rws).unwrap(),

            Some(VMMessage::Invocation {
                message, 
                entry_point,
                contract_address, 
                code_id
            }) => match entry_point {
                InstantiatedEntryPoint::Execute => VMManager::instantiate_vm(msg.tx_block_id, schedule,  &thread_exec_context, *code_id, contract_address, message.as_slice(), contract_address.clone(), 
                    rws, VMCall::Execute ).unwrap(),
                InstantiatedEntryPoint::Query   => VMManager::instantiate_vm(msg.tx_block_id, schedule, &thread_exec_context, *code_id, contract_address, message.as_slice(), contract_address.clone(), 
                    rws, VMCall::Query   ).unwrap(),
                InstantiatedEntryPoint::Reply => String::from(""),
            },
            None => unreachable!("RWSContext doesn't have a message set during block execution!"), // Should never happen
        }
    }

    /// Used on contract instantiations to compile the code
    fn compile_instantiate_vm(tx_block_id: u16, schedule: Arc<ConcurrentSchedule>, thread_exec_context: &ThreadExecutionContext<A, S, Q>, 
            contract_code_id: u128, msg: &[u8], rws: Vec<ReadWrite>) -> std::io::Result<String> {
        // Create the compiled module
        let code = thread_exec_context.state_manager.read().unwrap().get_code(contract_code_id)?;
        let engine = Box::new(make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT)));
        let module = Arc::new(compile( &engine, code.as_slice()).unwrap());
        let partitioned_storage = Arc::new(S::new());
        let backend = Arc::new((thread_exec_context.backend_builder)(partitioned_storage));
        
        // get deterministic address
        let address = (thread_exec_context.address_mapper)(
            contract_code_id, 
            thread_exec_context.state_manager.read().unwrap().get_instantiation_count(contract_code_id)
        );

        // save instance
        thread_exec_context.state_manager.read().unwrap().save_instance(
            address.clone(), 
            contract_code_id, 
            module, 
            Arc::clone(&backend));

        // build runtime intformation to execute
        let instance_data = thread_exec_context.state_manager.read().unwrap().get_instance_data(&address).unwrap();
        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
        let engine = make_runtime_engine(Some(DEFAULT_MEMORY_LIMIT));
        let store = Store::new(engine);
        
        // For Instantiation calls we don't yet have the SC storage partitioned.
        // Also, there is only 1 instantiation for some SC, so it doesnt make much sense to partition since there will be only 1 call
        // Thus the HashSet::new() -> no partitioned items
        let concurrent_backend = ConcurrentBackend::<A, MockStorageWrapper, Q>::new(tx_block_id, schedule,
            instance_data.state, address, rws);

        let mut instance = instance_from_module(
            store, 
            &instance_data.compiled_code, 
            concurrent_backend, 
            much_gas.gas_limit, 
            None).unwrap();

        let resp = call_instantiate::<_, _, _, Empty>(
            &mut instance, 
            &mock_env(), 
            &mock_info("", &[]), 
            msg
        ).unwrap();

        Ok(format!("{:?}", resp))
    }

    /// Used to instantiate an already deployed/compiled contract with 
    /// already created storage
    fn instantiate_vm(tx_block_id: u16,  schedule: Arc<ConcurrentSchedule>, thread_exec_context: &ThreadExecutionContext<A, S, Q>, code_id: u128, contract_address: &String, 
        message: &[u8], sc_address: String, rws: Vec<ReadWrite>, call_type: VMCall) -> std::io::Result<String> {
        let instance_data = thread_exec_context.state_manager.read().unwrap().get_instance_data(&contract_address).unwrap();

        let code = thread_exec_context.state_manager.read().unwrap().get_code(code_id)?;
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        // TODO - we should fetch this module from the instance_data variable!!
        let module = Arc::new(Box::new(compile( &engine, code.as_slice()).unwrap()));
        let store = Store::new(engine);

        let concurrent_backend = ConcurrentBackend::<A, MockStorageWrapper, Q>::new(tx_block_id, schedule,
            instance_data.state, sc_address, rws);

        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
        let mut instance = instance_from_module(
            store, 
            &module, 
            concurrent_backend,
            much_gas.gas_limit,
            None).unwrap();

        Ok(match call_type {
            VMCall::Execute => {
                let resp = call_execute::<_, _, _, Empty>(&mut instance, &mock_env(), &mock_info("", &[]), message).unwrap();
                format!("{:?}", resp)
            },
            VMCall::Query => {
                let resp = call_query::<_, _, _>(&mut instance, &mock_env(), message);
                String::from_utf8(base64::decode(resp.unwrap().unwrap().to_string()).unwrap()).unwrap()
            },
        })
    }
}


#[cfg(test)]
mod tests {
    use std::{collections::{HashMap, HashSet}, sync::{Arc, RwLock}};

    use cosmwasm_std::{ContractResult, Empty, Response};
    use serial_test::serial;
    use wasmer::Store;

    use crate::{
        backend::ConcurrentBackend, call_instantiate, internals::instance_from_module, symb_exec::{Commutativity, Key, ReadWrite, StorageDependency, TxRWS}, testing::{mock_env, mock_info, mock_persistent_backend, MockApi, MockQuerier, MockConcurrentStorage, MockStorageWrapper}, vm_manager::vm_manager::{RWSContext, ThreadExecutionContext, VMCall, DEFAULT_MEMORY_LIMIT, HIGH_GAS_LIMIT}, wasm_backend::{compile, make_compiling_engine, make_runtime_engine}, ConcurrentSchedule, InstanceOptions, InstantiatedEntryPoint, SCManager, SEStatus, VMMessage
    };

    use super::{AddressMapper, BackendBuilder, VMManager};

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");


    fn mock_backend_builder() -> Arc<BackendBuilder<MockApi, MockConcurrentStorage, MockQuerier>> {
        Arc::new(|storage| {
            mock_persistent_backend(&[], storage)
        })
    }

    fn mock_address_mapper() -> Arc<AddressMapper> {
        let mut mapping: HashMap<u128, HashMap<u128, String>> = HashMap::from([(0, HashMap::new())]);
        mapping.get_mut(&0).unwrap().insert(0, "a".to_owned());
        mapping.get_mut(&0).unwrap().insert(1, "b".to_owned());

        Arc::new(move |contract_code_id: u128, instantiation: u128| {
            mapping.get(&contract_code_id).unwrap().get(&instantiation).unwrap().clone()
        })
    }

    fn mock_vm_manager() -> VMManager<MockApi, MockConcurrentStorage, MockQuerier> {
        let state_manager: SCManager<MockApi, MockConcurrentStorage, MockQuerier> = SCManager::new();
        // simulate installing a contract
        state_manager.save_code(CONTRACT).unwrap();

        let state_manager = Arc::new(RwLock::new(state_manager));
        VMManager::new(
            Arc::clone(&state_manager), 
            mock_address_mapper(),
            mock_backend_builder(),
        )
    }

    #[test]
    fn address_mapper() {
        let state_manager: SCManager<MockApi, MockConcurrentStorage, MockQuerier> = SCManager::new();
        let mut mapping: HashMap<u128, HashMap<u128, String>> = HashMap::from([
            (0, HashMap::new()),
            (1, HashMap::new())
        ]);

        mapping.get_mut(&0).unwrap().insert(0, "a".to_owned());
        mapping.get_mut(&0).unwrap().insert(1, "b".to_owned());
        mapping.get_mut(&1).unwrap().insert(0, "c".to_owned());
        mapping.get_mut(&1).unwrap().insert(1, "d".to_owned());

        let address_mapper = move |contract_code_id: u128, instantiation: u128| {
            mapping.get(&contract_code_id).unwrap().get(&instantiation).unwrap().clone()
        };



        let vm_manager = VMManager::new(
            Arc::new(RwLock::new(state_manager)), 
            Arc::new(address_mapper),
            mock_backend_builder(),
        );

        assert_eq!((vm_manager.address_mapper)(0, 0), "a");
        assert_eq!((vm_manager.address_mapper)(0, 1), "b");
        assert_eq!((vm_manager.address_mapper)(1, 0), "c");
        assert_eq!((vm_manager.address_mapper)(1, 1), "d");
    }

    #[test]
    #[serial]
    fn vanilla_instantiation() {
        // save initial code -> will have code_id = 0
        let state_manager = SCManager::new();
        state_manager.save_code(CONTRACT).unwrap();

        assert_eq!(state_manager.get_code(0).unwrap(), CONTRACT);
        
        // Create the compiled module & storage
        let code = state_manager.get_code(0).unwrap();
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        let module = compile( &engine, code.as_slice()).unwrap();
        let partitioned_storage = Arc::new(MockConcurrentStorage::default());
        let backend = Arc::new(mock_persistent_backend(&[], partitioned_storage));

        // save instance
        state_manager.save_instance(
            "a".to_owned(),
            0,
            Arc::new(module),
            backend);

        let instance = state_manager.get_instance_data(&"a".to_owned()).unwrap();

        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT, };
        let engine = make_runtime_engine(Some(DEFAULT_MEMORY_LIMIT));
        let store = Store::new(engine);

        let rws = vec![];
        let concurrent_backend = ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(0, Arc::new(ConcurrentSchedule::new()),
            instance.state, String::from(""), rws);

        let mut instance = instance_from_module(
            store, 
            &instance.compiled_code, 
            concurrent_backend, 
            much_gas.gas_limit, 
            None
        ).unwrap();

        let msg = br#"{}"#;

        let contract_res = call_instantiate::<_, _, _, Empty>(
            &mut instance, 
            &mock_env(), 
            &mock_info("", &[]), 
            msg
        );

        assert_eq!(contract_res.unwrap(), ContractResult::Ok(Response::new()));
        assert_eq!(state_manager.get_instantiation_count(0), 1);

        state_manager.cleanup();
    }

    #[test]
    #[serial]
    fn instantiate_vm() {
        let vm_manager = mock_vm_manager();

        let msg = br#"{}"#;
        let thread_ctx = vm_manager.get_execution_context();
        let resp = VMManager::compile_instantiate_vm(0, Arc::new(ConcurrentSchedule::new()), &thread_ctx, 0, msg, vec![]).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        vm_manager.state_manager.read().unwrap().cleanup();
    }

    #[test]
    #[serial]
    fn execute_vm_untracked_operations() {
        let vm_manager = mock_vm_manager();
        let schedule = Arc::new(ConcurrentSchedule::new());

        let msg = br#"{}"#;
        let thread_ctx = vm_manager.get_execution_context();
        let resp = VMManager::compile_instantiate_vm(0, Arc::clone(&schedule), &thread_ctx, 0, msg, vec![]).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        let msg = br#"{
            "AddOne": {}
        }"#;
        let thread_ctx = vm_manager.get_execution_context();
        let resp = VMManager::instantiate_vm(0, Arc::clone(&schedule), &thread_ctx, 0, &String::from("a"), msg, 
                    String::from(""), vec![], VMCall::Execute).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);
        vm_manager.state_manager.read().unwrap().cleanup();
    }

    #[test]
    #[serial]
    fn query_vm() {
        let vm_manager = mock_vm_manager();

        let msg = br#"{}"#;
        let thread_ctx = vm_manager.get_execution_context();
        let resp = VMManager::compile_instantiate_vm(0, Arc::new(ConcurrentSchedule::new()),  &thread_ctx, 0, msg, vec![]).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        let msg = br#"{
            "GetBalance": {}
        }"#;
        let resp = VMManager::instantiate_vm(0, Arc::new(ConcurrentSchedule::new()), &thread_ctx, 0, &String::from("a"), msg,  
                    String::from(""), vec![], VMCall::Query).unwrap();
        assert_eq!("{\"balance\":1000}", resp);

        vm_manager.state_manager.read().unwrap().cleanup();
        
    }

    #[test]
    #[serial]
    fn persistent_calls() {
        let mut vm_manager = mock_vm_manager();

        let msgs = vec![
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            },
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            },
        ];

        let invocations = vec![
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "a".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "a".to_owned(),
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "a".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "b".to_owned(),
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "a".to_owned(),
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "a".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "b".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "a".to_owned(),
                message: br#"{
                    "AddUser": {
                        "admin": "Balelas"
                    }
                }"#.to_vec(),
                code_id: 0,
            },
        ];

        let resps = vm_manager.handle_block(msgs).unwrap();
        let resps = vm_manager.handle_block(invocations).unwrap();
        
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[0]);
        assert_eq!("{\"balance\":1000}", resps[1]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[2]);
        assert_eq!("{\"balance\":1001}", resps[3]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[4]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[5]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[6]);
        assert_eq!("{\"balance\":1002}", resps[7]);
        assert_eq!("{\"balance\":1001}", resps[8]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[9]);

        vm_manager.state_manager.read().unwrap().cleanup();

    }


    #[test]
    #[serial]
    fn get_rws() {
        let mut vm_manager = mock_vm_manager();

        let msgs = vec![
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            },
        ];

        // instantiate first, to create storage
        vm_manager.handle_block(msgs).unwrap();

        // only after having storage created
        let vm_message = VMMessage::Invocation {
            entry_point: InstantiatedEntryPoint::Execute,
            contract_address: "a".to_owned(),
            message: br#"{
                "AddOne": {}
            }"#.to_vec(),
            code_id: 0,
        };
        let msgs = vec![
            vm_message.clone()
        ];

        let rws = vm_manager.get_rws(msgs);
        assert_eq!(
            rws,
            vec![RWSContext {
                address: "a".to_owned(),
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws: vec![
                        ReadWrite::Read {
                            storage_dependency: StorageDependency::Independent,
                            key: Key::Bytes(vec![0, 4, 98, 97, 110, 107, 65, 68, 77, 73, 78]),
                            commutativity: Commutativity::Commutative,
                            operation_node: None,
                        },
                        ReadWrite::Write {
                            storage_dependency: StorageDependency::Independent,
                            key: Key::Bytes(vec![0, 4, 98, 97, 110, 107, 65, 68, 77, 73, 78]),
                            commutativity: Commutativity::Commutative,
                            operation_node: None,
                        },
                    ]
                },
                tx_message: Some(vm_message),
                tx_block_id: 0,
            }]
        );
        
        vm_manager.state_manager.read().unwrap().cleanup();
    }
}