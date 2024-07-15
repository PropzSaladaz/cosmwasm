use std::{collections::HashMap, sync::{Arc, Mutex, RwLock}, thread};

use cosmwasm_std::{Api, CustomQuery, Empty, QuerierWrapper};
use wasmer::Store;

use crate::{
    backend::ConcurrentBackend, call_execute, call_instantiate, call_query, internals::instance_from_module, 
    symb_exec::{ReadWrite, SEStatus, StorageDependency, TxRWS}, 
    testing::{mock_env, mock_info, ConcurrentStorage, MockStorageWrapper}, 
    wasm_backend::{compile, make_compiling_engine, make_runtime_engine}, 
    BackendApi, ConcurrentSchedule, InstanceOptions, Querier, SCProfile, Size, TxId
};

use super::sc_storage::{PersistentBackend, SCManager};

const DEFAULT_MEMORY_LIMIT: Size = Size::mebi(64);
const HIGH_GAS_LIMIT: u64 = 20_000_000_000_000_000; // ~20s, allows many calls on one instance

#[cfg(feature = "exec_time")]
use std::time::{Duration, Instant};


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

    n_threads: u16,

    #[cfg(feature = "debug_graph")]
    block_number: u128,

    #[cfg(feature = "exec_time")]
    schedule_timer: Option<Instant>,
    #[cfg(feature = "exec_time")]
    block_execution_timer: Option<Instant>,
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
    pub tx_block_id: TxId,

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
        backend_builder: Arc<BackendBuilder<A, S, Q>>, n_threads: u16) -> Self
    {
        VMManager {
            state_manager,
            address_mapper,
            backend_builder,
            n_threads,

            #[cfg(feature = "debug_graph")]
            block_number: 0,

            #[cfg(feature = "exec_time")]
            schedule_timer: None,
            #[cfg(feature = "exec_time")]
            block_execution_timer: None,
        }
    }

    #[cfg(feature = "debug_graph")]
    fn increase_current_block_counter(&mut self) {
        self.block_number += 1;
    }

    #[cfg(feature = "exec_time")]
    fn start_schedule_build_timer(&mut self) {
        self.schedule_timer = Some(Instant::now());
    }

    #[cfg(feature = "exec_time")]
    fn stop_schedule_build_timer(&mut self) -> Duration {
        self.schedule_timer.unwrap().elapsed()
    }

    #[cfg(feature = "exec_time")]
    fn start_block_execution_timer(&mut self) {
        self.block_execution_timer = Some(Instant::now());
    }

    #[cfg(feature = "exec_time")]
    fn stop_block_execution_timer(&mut self) -> Duration {
        self.block_execution_timer.unwrap().elapsed()
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

        #[cfg(feature = "exec_time")]
        self.start_schedule_build_timer();

        schedule.build_from_rws(&mut rws);

        #[cfg(feature = "exec_time")]
        {
            let elapsed_time = self.stop_schedule_build_timer();
            println!("\n\nExecTime ------\nSchedule Execution: {:?}", elapsed_time);
        }

        let resps = self.execute_block(rws, schedule).unwrap();
        
        #[cfg(feature = "debug_graph")]
        self.increase_current_block_counter();

        Ok(resps)
    }

    /// Get the RWS given an input message for some contract.
    /// Fetches the SE profile, parses it & gets the final RWS in form of keys as bytes
    /// It returns a vec where each item contains the contract address as well as all the keys
    /// it will touch
    /// The return vector places all COMPLETE & INDEPENDENT txs first, and only after all the INCOMPLETE or DEPENDENT txs
    fn get_rws(&self, block: Block) -> Vec<RWSContext> {
        let mut instantiations = vec![];
        let mut rws_complete_and_independent = vec![];
        let mut rws_incomplete_or_dependent = vec![];

        // this is different from the instantiation count from state_manager. This is just a mock.
        // We don't actually instantiate. And here we do it best case scenario - we assume every instantiaion
        // will 'work', and assign it a different SC address. We use this to get a unique address fo reach 
        // instantiation - to guarantee no conflicts between operations on the instantiated contract.
        let mut instantiation_counts: HashMap<u128, u128> = HashMap::new();

        for msg in block.into_iter() {
            match &msg {
                VMMessage::Instantiation { 
                    message, 
                    contract_code_id,
                } => {
                    // Increase instantiation count for each instantiate for the same code id
                    let instantiation_count = if let Some(count) = instantiation_counts.get_mut(contract_code_id) {
                            *count += 1;
                            *count
                        }
                        else {
                            instantiation_counts.insert(*contract_code_id, 0);
                            0
                    };
                        
                    let profile = self.state_manager.read().unwrap().get_profile(*contract_code_id);
                    let mut context = self.get_rws_instantiation(profile, message.as_slice(), 
                        *contract_code_id, instantiation_count);
                    context.tx_message = Some(msg);
                    instantiations.push(context);
                },

                VMMessage::Invocation { 
                    message, // ref is used not to move this field. Else, we would not be able to move it into the Some(msg) below
                    entry_point,
                    contract_address, 
                    code_id
                } => {
                    let profile = self.state_manager.read().unwrap().get_profile(*code_id);
                    match &self.state_manager.read().unwrap().get_instance_data(&contract_address) {
                        Some(sc_instance) => {
                            // Build mock depsMut
                            let storage = Arc::clone(&sc_instance.state.storage);
                            let mut context = self.get_rws_for_invocation(
                                                        &entry_point, profile, message.as_slice(), &contract_address, storage);
                            context.tx_message = Some(msg);

                            if (context.rws.profile_status == SEStatus::Complete) && (context.rws.storage_dependency == StorageDependency::Independent) {
                                rws_complete_and_independent.push(context);
                            }
                            else {
                                rws_incomplete_or_dependent.push(context);
                            }
                        }
                        // If invocation on a contract that wasn't yet instantiated
                        None => panic!("Invoquing execution on a contract that wasn't instantiated yet!")
                    }
                },
            };
        };
        // append incomplete || dependent RWSs at the end
        rws_complete_and_independent.append(&mut rws_incomplete_or_dependent);
        // set tx id as the index in the block
        for (idx, el) in rws_complete_and_independent.iter_mut().enumerate() {
            el.tx_block_id = idx as TxId;
        }

        rws_complete_and_independent
    }


    fn get_rws_instantiation(&self, profile: Arc<SCProfile>, message: &[u8], contract_code_id: u128, instantiation_count: u128) -> RWSContext {
        let querier = cosmwasm_std::testing::MockQuerier::default();
        let mut_deps = DepsMut { 
            storage: &S::new(), // creates empty storage for instantiates
            api: &cosmwasm_std::testing::MockApi::default(), 
            querier: cosmwasm_std::QuerierWrapper::new( &querier)
        };

        // set the contract's address given the predefined address from the trace
        let address = (self.address_mapper)(
            contract_code_id, 
            instantiation_count
        );

        RWSContext {
            rws: profile.get_rws_instantiate(&mut_deps, &mock_env(), &mock_info("", &[]), message),
            address: address,
            tx_message: None, // will be set by calling function
            tx_block_id: 0,   // will be set by calling function
        }
    }

    fn get_rws_for_invocation(&self, entry_point: &InstantiatedEntryPoint, profile: Arc<SCProfile>, message: &[u8],
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
        #[cfg(feature = "exec_time")]
        self.start_block_execution_timer();

        let mut handles = vec![];
        let resps = Arc::new(Mutex::new(vec![]));
        let schedule = Arc::new(schedule);
        let rws = Arc::new(rws);
        let thread_exec_ctx = Arc::new(VMManager::get_execution_context(&self));

        // execute each message
        for i in 0..self.n_threads {
            let schedule_ref = Arc::clone(&schedule);
            let resps_ref = Arc::clone(&resps);
            let rws_ref = Arc::clone(&rws);
            let thread_exec_ctx_ref = Arc::clone(&thread_exec_ctx);

            let handle = thread::spawn(move || {
                loop {
                    println!("Thread: {:?} waiting for message to execute", i);
                    if let Some(tx_id) = &schedule_ref.get_next_message_to_execute() {
                        println!("Thread: {:?} executing {:?}", i, tx_id);
                        let message = &rws_ref[*tx_id as usize];
                        // TODO - below clone should be optimized - no need.. we can pass a reference, or just return the same arc from the method
                        let resp = VMManager::execute_message(Arc::clone(&schedule_ref), &*thread_exec_ctx_ref, message, *tx_id);
                        
                        // TODO below line should be put inside the execute_message function ^^
                        schedule_ref.on_tx_finish(*tx_id);

                        println!("ready queue after thread {:?} execution of msg {:?}: {:#?}", i, tx_id, schedule_ref.ready_queue);

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

        self.persist_schedule(&schedule);

        #[cfg(feature = "exec_time")]
        {
            let elapsed_time = self.stop_block_execution_timer();
            println!("\nBlock Execution: {:?}\n------\n\n", elapsed_time);
        }

        // do not unclude graph generation in the execution time
        #[cfg(feature = "debug_graph")]
        schedule.generate_debug_graph(self.block_number, rws);

        // return the response vector contents
        let mut guard = resps.lock().unwrap();
        Ok(std::mem::take(&mut *guard))
    }

    fn persist_schedule(&self, concurrent_schedule: &Arc<ConcurrentSchedule>) {
        let sc_storage_manager_lock = self.state_manager.read().unwrap();
        concurrent_schedule.persist_schedule(&*sc_storage_manager_lock);
    }

    fn execute_message(schedule: Arc<ConcurrentSchedule>, thread_exec_context: &ThreadExecutionContext<A, S, Q>, 
        msg: &RWSContext, tx_id: TxId) -> String {
        // TODO - try passing a reference here -> we need to change later on the backend and mocksStorage to handle references instead of
        // Vec. Cloning the entire RWS is very innefficient here..
        let rws = msg.rws.rws.clone();

        let response = match &msg.tx_message {
            Some(VMMessage::Instantiation { 
                message, 
                contract_code_id,
            }) => VMManager::compile_instantiate_vm(msg.tx_block_id, &msg.address, schedule, &thread_exec_context, *contract_code_id, message.as_slice(), rws).unwrap(),

            Some(VMMessage::Invocation {
                message, 
                entry_point,
                contract_address, 
                code_id
            }) => match entry_point {
                InstantiatedEntryPoint::Execute => VMManager::instantiate_vm(msg.tx_block_id, schedule,  &thread_exec_context, *code_id, contract_address.clone(), message.as_slice(), 
                    rws, VMCall::Execute ).unwrap(),
                InstantiatedEntryPoint::Query   => VMManager::instantiate_vm(msg.tx_block_id, schedule, &thread_exec_context, *code_id, contract_address.clone(), message.as_slice(),
                    rws, VMCall::Query   ).unwrap(),
                InstantiatedEntryPoint::Reply => String::from(""),
            },
            None => unreachable!("RWSContext doesn't have a message set during block execution!"), // Should never happen
        };

        response
    }

    /// Used on contract instantiations to compile the code
    fn compile_instantiate_vm(tx_block_id: TxId, address: &String, schedule: Arc<ConcurrentSchedule>, thread_exec_context: &ThreadExecutionContext<A, S, Q>, 
            contract_code_id: u128, msg: &[u8], rws: Vec<ReadWrite>) -> std::io::Result<String> {
        // Create the compiled module
        let code = thread_exec_context.state_manager.read().unwrap().get_code(contract_code_id)?;
        let engine = Box::new(make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT)));
        let module = Arc::new(compile( &engine, code.as_slice()).unwrap());
        let partitioned_storage = Arc::new(S::new());
        let backend = Arc::new((thread_exec_context.backend_builder)(partitioned_storage));

        // save instance
        thread_exec_context.state_manager.read().unwrap().save_instance(
            address.clone(), 
            contract_code_id, 
            module, 
            Arc::clone(&backend));

        // build runtime information to execute
        let instance_data = thread_exec_context.state_manager.read().unwrap().get_instance_data(&address).unwrap();
        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
        let engine = make_runtime_engine(Some(DEFAULT_MEMORY_LIMIT));
        let store = Store::new(engine);
        
        let concurrent_backend = ConcurrentBackend::<A, MockStorageWrapper, Q>::new(tx_block_id, schedule,
            instance_data.state, address.clone(), rws);

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
    fn instantiate_vm(tx_block_id: TxId,  schedule: Arc<ConcurrentSchedule>, thread_exec_context: &ThreadExecutionContext<A, S, Q>, code_id: u128, contract_address: String, 
        message: &[u8], rws: Vec<ReadWrite>, call_type: VMCall) -> std::io::Result<String> {
        let instance_data = thread_exec_context.state_manager.read().unwrap().get_instance_data(&contract_address).unwrap();

        let code = thread_exec_context.state_manager.read().unwrap().get_code(code_id)?;
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        // TODO - we should fetch this module from the instance_data variable!!
        let module = Arc::new(Box::new(compile( &engine, code.as_slice()).unwrap()));
        let store = Store::new(engine);

        let concurrent_backend = ConcurrentBackend::<A, MockStorageWrapper, Q>::new(tx_block_id, schedule,
            instance_data.state, contract_address, rws);

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
    use std::{collections::HashMap, sync::{Arc, RwLock}};

    use cosmwasm_std::{ContractResult, Empty, Response};
    use serial_test::serial;
    use wasmer::Store;

    use crate::{
        backend::ConcurrentBackend, call_instantiate, internals::instance_from_module, 
        symb_exec::{Commutativity, Key, ReadWrite, StorageDependency, TxRWS}, 
        testing::{mock_env, mock_info, mock_persistent_backend, mock_tx_operation, MockApi, MockConcurrentStorage, MockQuerier, MockStorageWrapper}, 
        vm_manager::vm_manager::{RWSContext, VMCall, DEFAULT_MEMORY_LIMIT, HIGH_GAS_LIMIT}, 
        wasm_backend::{compile, make_compiling_engine, make_runtime_engine}, 
        ConcurrentSchedule, InstanceOptions, InstantiatedEntryPoint, SCManager, SEStatus, VMMessage
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
        mapping.get_mut(&0).unwrap().insert(2, "c".to_owned());
        mapping.get_mut(&0).unwrap().insert(3, "d".to_owned());

        Arc::new(move |contract_code_id: u128, instantiation: u128| {
            mapping.get(&contract_code_id).unwrap().get(&instantiation).unwrap().clone()
        })
    }

    fn mock_vm_manager(n_threads: u16) -> VMManager<MockApi, MockConcurrentStorage, MockQuerier> {
        let state_manager: SCManager<MockApi, MockConcurrentStorage, MockQuerier> = SCManager::new();
        // simulate installing a contract
        state_manager.save_code(CONTRACT).unwrap();

        let state_manager = Arc::new(RwLock::new(state_manager));
        VMManager::new(
            Arc::clone(&state_manager), 
            mock_address_mapper(),
            mock_backend_builder(),
            n_threads
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
            1
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
        
        // schedule needs at least 1 operation to know the tx
        let mut schedule = ConcurrentSchedule::new();
        schedule.build_from_rws(&mut vec![
            mock_tx_operation(&"a".to_owned(), &vec![1u8], 0, ReadWrite::write(), Commutativity::NonCommutative)
        ]);

        let concurrent_backend = ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(0, Arc::new(schedule),
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
    fn vanilla_sequential_instantiate_vm() {
        let vm_manager = mock_vm_manager(1);

        let msg = br#"{}"#;
        let thread_ctx = vm_manager.get_execution_context();
        
        // schedule needs at least 1 operation to know the tx
        let mut schedule = ConcurrentSchedule::new();
        schedule.build_from_rws(&mut vec![
            mock_tx_operation(&"a".to_owned(), &vec![1u8], 0, ReadWrite::write(), Commutativity::NonCommutative)
        ]);
        let resp = VMManager::compile_instantiate_vm(0, &"a".to_owned(), Arc::new(schedule), &thread_ctx, 0, msg, vec![]).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        vm_manager.state_manager.read().unwrap().cleanup();
    }
    

    #[test]
    #[serial]
    fn vanilla_sequential_execute_vm_untracked_operations() {
        let vm_manager = mock_vm_manager(1);
        let mut schedule = ConcurrentSchedule::new();
        let sc_address = String::from("a"); // needs to be "a" since this is the address created by the mock_vm_manager()

        // every tx needs to be detected when building the schedule. So we need a random operation for it to be detected
        schedule.build_from_rws(&mut vec![
            mock_tx_operation(&String::from("a"), &vec![1u8], 0, ReadWrite::write(), Commutativity::NonCommutative)
        ]);

        let schedule = Arc::new(schedule);

        let msg = br#"{}"#;
        let thread_ctx = vm_manager.get_execution_context();
        let resp = VMManager::compile_instantiate_vm(0, &"a".to_owned(), Arc::clone(&schedule), &thread_ctx, 0, msg, vec![]).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        let msg = br#"{
            "AddOne": {}
        }"#;
        let thread_ctx = vm_manager.get_execution_context();
        let resp = VMManager::instantiate_vm(0, Arc::clone(&schedule), &thread_ctx, 0, sc_address, msg, 
        vec![], VMCall::Execute).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        vm_manager.state_manager.read().unwrap().cleanup();
    }

    #[test]
    #[serial]
    fn sequential_query_vm() {
        let vm_manager = mock_vm_manager(1);

        let msg = br#"{}"#;
        let thread_ctx = vm_manager.get_execution_context();

        // schedule needs at least 1 operation to know the tx
        let mut schedule = ConcurrentSchedule::new();
        schedule.build_from_rws(&mut vec![
            mock_tx_operation(&"a".to_owned(), &vec![1u8], 0, ReadWrite::write(), Commutativity::NonCommutative)
        ]);
        let schedule = Arc::new(schedule);

        let resp = VMManager::compile_instantiate_vm(0, &"a".to_owned(), Arc::clone(&schedule),  &thread_ctx, 0, msg, vec![]).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        let msg = br#"{
            "GetBalance": {}
        }"#;
        let resp = VMManager::instantiate_vm(0, Arc::clone(&schedule), &thread_ctx, 0, String::from("a"), msg,  
            vec![], VMCall::Query).unwrap();
        assert_eq!("{\"balance\":1000}", resp);

        vm_manager.state_manager.read().unwrap().cleanup();
        
    }



    #[test]
    #[serial]
    fn get_rws() {
        let mut vm_manager = mock_vm_manager(1);

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


    #[test]
    #[serial]
    fn sequential_persistent_calls() {
        let mut vm_manager = mock_vm_manager(1);

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

        // We ordered this by order of the scheduled execution. Not that conceptually
        // we would execute 4th message right after the 2nd to confirm the incremented value on contract 'a'
        // but since there is a dependency, the 4th will only execute after all txs with no dependencies.
        // Meaning the 3rd message will run before the 4th message
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
                    "AddUser": {
                        "admin": "Balelas"
                    }
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
        ];

        vm_manager.handle_block(msgs).unwrap();
        let resps = vm_manager.handle_block(invocations).unwrap();

        assert_eq!("{\"balance\":1000}", resps[0]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[1]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[2]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[3]);

        // the 4th and 5th operations may interchange nondeterministically. This is because we use 
        // a HashSet to store the dependent txs. Since 3rd & 4th operations depend on the 2nd,
        // then when we execute these, any order is possible - there are no conflicts between them
        if resps[4].starts_with("{\"balance\"") {
            assert_eq!("{\"balance\":1001}", resps[4]);         
            assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[5]);
        }
        else {        
            assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[4]);
            assert_eq!("{\"balance\":1001}", resps[5]); 
        }


        assert_eq!("{\"balance\":1001}", resps[6]);
        assert_eq!("{\"balance\":1002}", resps[7]);

        vm_manager.state_manager.read().unwrap().cleanup();

    }



    #[test]
    // #[ignore]
    #[serial]
    fn parallel_workload_test() {
        let mut vm_manager = mock_vm_manager(4);

        let msgs = vec![
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            },
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            },
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            },
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            },
        ];
        vm_manager.handle_block(msgs).unwrap();

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
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "b".to_owned(),
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "c".to_owned(),
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "d".to_owned(),
                message: br#"{
                    "AddOne": {}
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
                contract_address: "d".to_owned(),
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
                contract_address: "c".to_owned(),
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
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "d".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            },
        ];

        vm_manager.handle_block(invocations).unwrap();


        // 1 query at a time to enforce serializability to allow comparing received response with predicted
        let invocation = vec![
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "a".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            },
        ];
        let resp = vm_manager.handle_block(invocation).unwrap();
        assert_eq!("{\"balance\":1002}", resp[0]);


        // 1 query at a time to enforce serializability to allow comparing received response with predicted
        let invocation = vec![
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "b".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            },
        ];
        let resp = vm_manager.handle_block(invocation).unwrap();
        assert_eq!("{\"balance\":1001}", resp[0]);

        let invocation = vec![
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "c".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            },
        ];
        let resp = vm_manager.handle_block(invocation).unwrap();
        assert_eq!("{\"balance\":1001}", resp[0]);

        let invocation = vec![
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "d".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            },
        ];
        let resp = vm_manager.handle_block(invocation).unwrap();
        assert_eq!("{\"balance\":1002}", resp[0]);

        vm_manager.state_manager.read().unwrap().cleanup();

    }

}