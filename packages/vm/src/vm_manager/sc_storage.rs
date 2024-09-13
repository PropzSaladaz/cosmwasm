use std::{collections::{HashMap, VecDeque}, fs::{self, File}, hash::Hash, io::{ErrorKind, Read, Write}, sync::{Arc, RwLock}, thread};
use std::io::Error;

use cosmwasm_std::{ContractResult, Response};
use parking_lot::{Condvar, Mutex};

use dashmap::DashMap;
use wasmer::Module;

use crate::{ 
    backend::ConcurrentBackend, print_with_thread_id, symb_exec::{ProfileEvaluator, ProfileGenerator, SEEngine, SEEngineParse}, testing::{mock_backend, ConcurrentStorage, MockApi, MockConcurrentStorage, MockQuerier, StorageWrapper}, BackendApi, Instance, Querier, SCProfile, SCProfileParser, Storage, VmResult};

use super::schedule::{ScAddr, TxId};



const SMART_CONTRACT_PATH: &'static str = "./wasm_contract_codes";

fn contract_path(id: u128) -> String {
    SMART_CONTRACT_PATH.to_string() + "/" + &id.to_string() + ".wasm"
}


/// Represents static data (need only to store 1 for each contract code) 
/// for each contract.
/// There will only be 1 code for each different SC bytecode. This stores:
/// 
/// - SC Profile for each SC: tree-like structure with all possible RWS given the tx inputs (may be incomplete)
/// - Current SC code id: Monotonically increasing int (given all previous SCs that were installed)
/// - Instantiation Count: How many times a SC was instantiated. Also monotonically increasing
#[derive(Debug)]
struct SCStaticData {
    sc_code_id: u128,
    /// Stores SCProfile for each different SC code.
    profiles: HashMap<u128, Arc<SCProfile>>,
    /// Maps sc_addresses to code ids
    address_code_id: HashMap<ScAddr, u128>,
    /// Stores number of instantiated SCs per contract_id
    instantiation_count: Arc<Mutex<HashMap<u128, u128>>>,
}

impl SCStaticData {
    pub fn new() -> Self {
        Self {
            sc_code_id: 0,
            profiles: HashMap::new(),
            address_code_id: HashMap::new(),
            instantiation_count: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    pub fn incr_instantiation(&self, code_id: u128) {
        self.instantiation_count.lock()
            .entry(code_id).and_modify(|count| *count += 1);
    }

    pub fn get_instantiation_count(&self, code_id: u128) -> u128 {
        match self.instantiation_count.lock().get(&code_id) {
            Some(count) => *count,
            None => 0,
        }
    }

    /// Should be called for each instantiation to allow getting SC codes by the address
    pub fn link_address_to_code(&mut self, code_id: u128, sc_addr: &ScAddr) {
        self.address_code_id.insert(*sc_addr, code_id);
    }

    /// Saves a SC code. Uses the Symb Engine to produce a RWS profile
    /// for the contract and saves the profile information for this contract.
    /// Sets instantiation count for this new SC code to 1
    pub fn save<E: ProfileGenerator>(&mut self, sc_code: &[u8], code_id: Option<u128>, symb_exec: &Arc<E>) -> std::io::Result<u128> {
        let curr_dir = std::env::current_dir()?;
        let rel_path = curr_dir.join(contract_path(self.sc_code_id));
        let mut file_writer = File::create(rel_path)?;
        file_writer.write_all(sc_code)?;

        let sc_profile = symb_exec.generate_profile(sc_code);

        let code_id = if let Some(code_id) = code_id {
            // we are replaying, since we already know the code_id in advance
            self.profiles.insert(code_id, Arc::new(sc_profile));
            self.instantiation_count.lock().insert(code_id, 0);
            code_id
        }
        else {
            // we are not replaying - we don't know the code_id
            self.profiles.insert(self.sc_code_id, Arc::new(sc_profile));        
            self.instantiation_count.lock().insert(self.sc_code_id, 0);
            let id = self.sc_code_id;
            self.sc_code_id += 1;
            id
        };
        
        Ok(code_id)
    }

    pub fn get_code(&self, code_id: u128) -> std::io::Result<Vec<u8>> {
        let curr_dir = std::env::current_dir()?;
        let rel_path = curr_dir.join(contract_path(code_id));
        let mut f = File::open(rel_path)?;
        let mut code: Vec<u8> = vec![];
        f.read_to_end(&mut code)?;
        Ok(code)
    }

    pub fn get_code_by_address(&self, address: ScAddr) -> std::io::Result<Vec<u8>> {
        let code_id = self.address_code_id.get(&address).unwrap();
        self.get_code(*code_id)
    }

    pub fn get_profile(&self, code_id: u128) -> Result<Arc<SCProfile>, String> {
        match self.profiles.get(&code_id) {
            Some(profile) => Ok(Arc::clone(profile)),
            None => Err("Profile doesn't exist".to_string()) 
        }
    }

    pub fn get_profile_by_address(&self, sc_addr: &ScAddr) -> Result<Arc<SCProfile>, String> {
        let code_id = self.address_code_id.get(sc_addr).unwrap();
        self.get_profile(*code_id)
    }

    fn cleanup(&mut self) {
        for id in 0..self.sc_code_id {
            fs::remove_file(contract_path(id)).unwrap();
        }
    } 
}



/// Stores persistent information about the SC state.
/// The most important is Storage. Keeps track of a reference to the storage
/// of a SC
#[derive(Clone, Debug)]
pub struct PersistentBackend<A, S, Q> 
where
    A: BackendApi, 
    S: ConcurrentStorage, 
    Q: Querier
{
    pub api: Arc<A>,
    pub storage: Arc<S>,
    pub querier: Arc<RwLock<Q>>,
}

impl<A, S, Q> PersistentBackend<A, S, Q>
where
    A: BackendApi, 
    S: ConcurrentStorage, 
    Q: Querier
{
    pub fn default() -> PersistentBackend<MockApi, MockConcurrentStorage, MockQuerier> {
        PersistentBackend {
            api: Arc::new(MockApi::default()),
            storage: Arc::new(MockConcurrentStorage::default()),
            querier: Arc::new(RwLock::new(MockQuerier::new(&[("", &[])]))),
        }
    }
}



struct FairLock<T> {
    queue: Mutex<VecDeque<usize>>, // Queue of operations
    condvar: Condvar,
    resource: Mutex<T>,            // The resource
}

impl<T> FairLock<T> {
    fn new(resource: T) -> Self {
        FairLock {
            queue: Mutex::new(VecDeque::new()),
            condvar: Condvar::new(),
            resource: Mutex::new(resource),
        }
    }

    fn lock(&self, tx_id: usize) -> parking_lot::MutexGuard<'_, T> {
        let mut queue = self.queue.lock();
        
        queue.push_back(tx_id);

        while queue.front() != Some(&tx_id) {
            
            self.condvar.wait(&mut queue);
        }

        #[cfg(feature = "debug")]
        print_with_thread_id!("Finish waiting on VM, starting execution");

        // Get the resource lock
        let guard = self.resource.lock();

        // Remove the thread from the queue and notify others
        queue.pop_front();
        self.condvar.notify_all();

        guard
    }
}




pub struct SCInstance<A, S, W, Q> // TEST - should be private 
where
    A: BackendApi, 
    S: ConcurrentStorage,
    W: StorageWrapper,
    Q: Querier
{
    code_id: u128, // Just to keep track of which code this contract was generated from
    pub state: Arc<PersistentBackend<A, S, Q>>,
    pub vm_instances: Arc<Vec<FairLock<Instance<A, W, Q>>>>,
}

impl<A, S, W, Q> SCInstance<A, S, W, Q> 
where
    A: BackendApi, 
    S: ConcurrentStorage,
    W: StorageWrapper, 
    Q: Querier
{
    fn new(code_id: u128, state: &Arc<PersistentBackend<A, S, Q>>, instances: Vec<FairLock<Instance<A, W, Q>>>) -> Self {
        Self {
            code_id,
            state: Arc::clone(state),
            vm_instances: Arc::new(instances),
        }
    }
}



/// Used after applying the algorithm that identifies the keys to partition.
/// Stores the RWS to partition per each SC. THe address is then used to fetch the storage
/// and to partition the annotated items.
#[derive(Clone, PartialEq, Debug)]
pub struct ContractRWS {
    pub rws: Vec<Vec<u8>>,
    pub address: String,
}


/// Struct that stores context data for persistent execution
/// over different cosmwasm vm instances.
///
/// Inlcudes both compiled module + SC state
pub struct InstanceData<A, S, Q> 
where
    A: BackendApi, 
    S: ConcurrentStorage, 
    Q: Querier
{
    pub state: Arc<PersistentBackend<A, S, Q>>,
    pub compiled_code: Arc<Module>,
}

/// Stores the SC's vm instance.
/// for each instantiated contract.
//                 SC address -> SC instantiation
type SCStorage<A, S, W, Q> = DashMap<ScAddr, Arc<SCInstance<A, S, W, Q>>>;

/// Entity responsible for managing Smart Contract state
/// 
/// This includes both static state - SC code & profile, as well as
/// the VM instances & the Storage for each SC.
/// 
/// It also keeps a reference of 'part' of the Symbolic execution engine
/// for generating the profiles. The other part (the Profile Evaluator) is
/// kepts in the VMManager itself, which is at a higher.
pub struct SCManager<A, S, W, Q, E> 
where
    A: BackendApi + 'static,
    S: ConcurrentStorage + 'static,
    W: StorageWrapper + 'static,
    Q: Querier + 'static,
    E: ProfileGenerator
{
    static_data: Arc<RwLock<SCStaticData>>,
    pub sc_storage: SCStorage<A, S, W, Q>,
    symb_exec_engine: Arc<E>
}

impl<A, S, W, Q, E> SCManager<A, S, W, Q, E> 
where
    A: BackendApi, 
    S: ConcurrentStorage, 
    W: StorageWrapper,
    Q: Querier,
    E: ProfileGenerator
{

    pub fn get_symb_exec_engine(&self) -> Arc<E> {
        Arc::clone(&self.symb_exec_engine)
    }

    pub fn new(symb_exec_engine: Arc<E>) -> SCManager<A, S, W, Q, E> {
        SCManager {
            static_data: Arc::new(RwLock::new(SCStaticData::new())),
            sc_storage: DashMap::new(),
            symb_exec_engine
        }
    }

    /// Saves the storage & compiled module that refers to some instantiated SC
    pub fn save_instance(&self, code_id: u128, address: ScAddr, state: Arc<PersistentBackend<A, S, Q>>, instances: Vec<Instance<A, W, Q>>) {
        let fair_lock_instances: Vec<FairLock<Instance<A, W, Q>>> = instances.into_iter()
            .map(|i| FairLock::new(i))
            .collect();

        self.sc_storage.insert(address, Arc::new(
            SCInstance::new(
                code_id,
                &state,
                fair_lock_instances)
            ));
        self.static_data.write().unwrap().incr_instantiation(code_id);
    }

    /// Executes something using a mutable reference of a cosmwasm instance.
    /// Tries locking one instance form a set of N instances.
    /// If none is available, then wait for the first one to finish.
    pub fn execute_instance<F>(&self, address: &ScAddr, concurrent_backend: ConcurrentBackend<A, W, Q>,  work_id: TxId, work: F) -> std::io::Result<String> 
    where
        F: FnOnce(&mut Instance<A, W, Q>) -> std::io::Result<String>,
    {
        // print_with_thread_id!("Inside execute in VM");

        match self.sc_storage.get(address) {
            Some(sc_instance) => {
                let instances = &sc_instance.vm_instances;
                let vm_to_use = work_id % instances.len();
                #[cfg(feature = "debug")]
                print_with_thread_id!("SC {:?} - Waiting for VM {:?} to be free!", address, vm_to_use);

                let mut forced_vm = instances[vm_to_use].lock(work_id);
                forced_vm.set_concurrent_backend(concurrent_backend);
                let res = work(&mut forced_vm);
                
                #[cfg(feature = "debug")]
                print_with_thread_id!("SC {:?} - Finished executing on VM", address);

                return Ok(res.unwrap());
            },
            None => Result::Err(Error::new(ErrorKind::Other, "Trying to execute an uninstanciated contract!".to_owned()))
        }
    }

    pub fn get_sc_storage(&self, address: &ScAddr) -> Option<Arc<PersistentBackend<A, S, Q>>> {
        match self.sc_storage.get(address) {
            Some(sc_instance) => Some(Arc::clone(&sc_instance.state)),
            None => None
        }
    }

    pub fn get_code(&self, code_id: u128) -> std::io::Result<Vec<u8>> {
        self.static_data.read().unwrap().get_code(code_id)
    }

    /// Should be called for each instantiation to allow getting SC codes by the address
    pub fn link_address_to_code(&self, code_id: u128, sc_addr: &ScAddr) {
        self.static_data.write().unwrap().link_address_to_code(code_id, sc_addr);
    }

    pub fn get_code_by_address(&self, sc_addr: ScAddr) -> std::io::Result<Vec<u8>> {
        self.static_data.read().unwrap().get_code_by_address(sc_addr)
    }

    /// Saves SC code in Filsystem & builds the respective Symb. Exec.
    /// tree for the contract
    pub fn save_code(&self, code: &[u8], code_id: Option<u128>) -> std::io::Result<()> {
        self.static_data.write().unwrap().save(code, code_id, &self.symb_exec_engine)?;
        Ok(())
    }

    pub fn get_instantiation_count(&self, code_id: u128) -> u128 {
        self.static_data.read().unwrap().get_instantiation_count(code_id)
    }

    pub fn get_profile(&self, code_id: u128) -> Arc<SCProfile> {
        self.static_data.read().unwrap().get_profile(code_id).unwrap()
    }

    pub fn get_profile_by_address(&self, sc_addr: &ScAddr) -> Arc<SCProfile> {
        self.static_data.read().unwrap().get_profile_by_address(sc_addr).unwrap()
    } 

    pub fn cleanup(&self) {
        self.static_data.write().unwrap().cleanup();
    }

    pub fn get_contract_storage(&self, sc_address: ScAddr) -> Arc<S> {
        let sc_storage = self.sc_storage.get(&sc_address).expect("Smart Contract should have been initialized");
        let storage = Arc::clone(&sc_storage.state.storage); // TODO we shouldn't have to clone. this should be done serially
        storage
    }
}





#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use cosmwasm_std::{ContractResult, Empty, Response};
    use serial_test::serial;
    use wasmer::Store;

    use crate::{
        call_execute, call_instantiate, internals::instance_from_module, symb_exec::{Commutativity, EntryPoint, ProfileGenerator, SEStatus}, testing::{mock_concurrent_backend, mock_env, mock_info, mock_persistent_backend, mock_tx_operation, MockApi, MockConcurrentStorage, MockQuerier, MockStorageWrapper}, vm_manager::serial_schedule::ScheduleBuilder, wasm_backend::{compile, make_compiling_engine, make_runtime_engine}, ConcurrentSchedule, InstanceOptions, ReadWrite, Size, SymbolicExecutionEngine
    };

    use super::*;

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");
    const HIGH_GAS_LIMIT: u64 = 20_000_000_000_000; // ~20s, allows many calls on one instance
    const DEFAULT_MEMORY_LIMIT: Size = Size::mebi(64);

    const SC_ADDR_A: ScAddr = *b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    #[test]
    #[serial]
    fn generics_test() {
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        let module = compile( &engine, CONTRACT).unwrap();
        let concurrent_store = Arc::new(MockConcurrentStorage::default());
        let backend = Arc::new(mock_persistent_backend(&[], Arc::clone(&concurrent_store)));

        let store = Store::new(engine);
        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
        let concurrent_backend = mock_concurrent_backend(&[], concurrent_store);
        let instance = instance_from_module(store, &module, concurrent_backend, much_gas.gas_limit, None).unwrap();
        let instances = vec![instance];

        let sc_manager = Arc::new(RwLock::new(SCManager::new(Arc::new(SymbolicExecutionEngine::new()))));
        sc_manager.write().unwrap().save_instance(0, SC_ADDR_A, backend, instances);

        sc_manager.write().unwrap().cleanup();
    }

    #[test]
    #[serial]
    fn sc_static_data_workflow() {
        let mut sc_static_data = SCStaticData::new();

        // of course contracts should be compiled wasm, but we just write
        // the output of the SE for simplicity of testing - we need only know
        // if value is actually written as a file
        let contract = br#"I ----------------------------

_deps: DepsMut
_env: Env
_info: MessageInfo
_msg: InstantiateMsg


[PC_1] True
=> SET(=AARiYW5rQURNSU4=): Non-Inc
<- None"#;

        let se_engine = SymbolicExecutionEngine::default();
        sc_static_data.save(contract.as_slice(), None, &Arc::new(se_engine)).unwrap();

        // Try reading saved contract code
        let content = sc_static_data.get_code(0).unwrap();
        assert_eq!(content, *contract);

        // check if SC_ID increased
        assert_eq!(sc_static_data.sc_code_id, 1);

        // compare the saved profile with the actual one
        let sc_profile_tmp = SCProfileParser::from_string(
            SEStatus::Complete,
            String::from_utf8(contract.to_vec()).unwrap());
        let instantiate_tmp = sc_profile_tmp.entry_point.get(&EntryPoint::Instantiate).unwrap();

        let sc_profile = sc_static_data.get_profile(0).unwrap();
        let instantiate = sc_profile.entry_point.get(&EntryPoint::Instantiate).unwrap();

        assert_eq!(instantiate_tmp, instantiate);


        // check instantiation counter logic
        sc_static_data.incr_instantiation(0);
        sc_static_data.incr_instantiation(0);

        assert_eq!(sc_static_data.get_instantiation_count(0), 2);

        sc_static_data.cleanup();
    }

    #[test]
    #[ignore]
    #[serial]
    fn sc_manager_workflow() {
        let sc_manager = SCManager::new(Arc::new(SymbolicExecutionEngine::new()));
        // save code
        sc_manager.save_code(CONTRACT, None).unwrap();

        let backend;

        let mut schedule = ScheduleBuilder::new();
        schedule.build_from_rws(&mut vec![
            mock_tx_operation(SC_ADDR_A, &vec![1u8], 0, ReadWrite::write(), Commutativity::NonCommutative)
        ]);
        let concurrent_schedule = Arc::new(ConcurrentSchedule::from_schedule_builder(schedule, 1));

        { // simulate saving instance in a separate context
            // compile code & create storage
            // get code
            let code = sc_manager.get_code(0).unwrap();
            let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
            let module = compile( &engine, code.as_slice()).unwrap();
            let concurrent_store = Arc::new(MockConcurrentStorage::default());
            backend = Arc::new(mock_persistent_backend(&[], Arc::clone(&concurrent_store)));

            // simulate instantiating N vms - we use runtime engine now, since we already got the module compiled.
            let engine = make_runtime_engine(Some(DEFAULT_MEMORY_LIMIT));
            let store = Store::new(engine);
            let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
            
            let concurrent_backend = ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(0, Arc::clone(&concurrent_schedule),
            Arc::clone(&backend), &SC_ADDR_A, vec![]);

            let instance = instance_from_module(store, &module, concurrent_backend, much_gas.gas_limit, None).unwrap();
            let instances = vec![instance];

            // save it to that SC code
            sc_manager.save_instance(
                0,
                SC_ADDR_A, 
                Arc::clone(&backend),
                instances
            );
        }

        // Instantiate
       
        { // simulate instantiate call in a separate context
            let rws = vec![];
            let concurrent_backend = ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(0, Arc::clone(&concurrent_schedule),
                Arc::clone(&backend), &SC_ADDR_A, rws);
    
            // execute instantiate contract
            let msg = br#"{}"#;
            let resp = sc_manager.execute_instance(&SC_ADDR_A, concurrent_backend, 0, |instance| {
                let contract_res = call_instantiate::<_, _, _, Empty>(
                    instance, 
                    &mock_env(), 
                    &mock_info("", &[]), 
                    msg
                ).unwrap();
                Ok(format!("{:?}", contract_res))
            });
    
            
            assert_eq!(resp.unwrap(), "Ok(\"Ok(Response { messages: [], attributes: [], events: [], data: None })\")".to_owned());
            assert_eq!(sc_manager.get_instantiation_count(0), 1);
        }

        { // simulate executing in a separate context
            // Execute
            let mut schedule = ScheduleBuilder::new();
            schedule.build_from_rws(&mut vec![
                mock_tx_operation(SC_ADDR_A, &vec![1u8], 0, ReadWrite::write(), Commutativity::NonCommutative)
            ]);
            
            let rws = vec![];
            let concurrent_backend = ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(0, Arc::clone(&concurrent_schedule),
                Arc::clone(&backend), &SC_ADDR_A, rws);

            // execute instantiate contract
            let msg = br#"{ 
                "AddOne": {} 
            }"#;
            let resp = sc_manager.execute_instance(&SC_ADDR_A, concurrent_backend, 0, |instance| {
                let contract_res = call_execute::<_, _, _, Empty>(
                    instance, 
                    &mock_env(), 
                    &mock_info("", &[]), 
                    msg
                ).unwrap();
                Ok(format!("{:?}", contract_res))
            });
            
            assert_eq!(resp.unwrap(), "Ok(\"Ok(Response { messages: [], attributes: [], events: [], data: None })\")".to_owned());
            assert_eq!(sc_manager.get_instantiation_count(0), 1);
        }


        sc_manager.cleanup();

    }

}