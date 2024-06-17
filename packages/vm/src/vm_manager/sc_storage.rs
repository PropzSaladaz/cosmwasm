use std::{collections::HashMap, fs::{self, File}, io::{Read, Write}, sync::{Arc, Mutex, RwLock}};

use dashmap::DashMap;
use wasmer::Module;

use crate::{ 
    backend::ConcurrentBackend, symb_exec::{SEEngine, SEEngineParse}, testing::PartitionedStorage, BackendApi, Querier, SCProfile, SCProfileParser, Storage};


const SMART_CONTRACT_PATH: &'static str = "./wasm_contract_codes";

fn contract_path(id: u128) -> String {
    SMART_CONTRACT_PATH.to_string() + "/" + &id.to_string() + ".wasm"
}


/// Represents static data (need only to store 1 for each contract code) 
/// for each contract.
#[derive(Debug)]
struct SCStaticData {
    sc_code_id: u128,
    profiles: HashMap<u128, Arc<SCProfile>>,
    instantiation_count: Arc<Mutex<HashMap<u128, u128>>>,
}

impl SCStaticData {
    pub fn new() -> Self {
        Self {
            sc_code_id: 0,
            profiles: HashMap::new(),
            instantiation_count: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    pub fn incr_instantiation(&self, code_id: u128) {
        self.instantiation_count.lock().unwrap()
            .entry(code_id).and_modify(|count| *count += 1);
    }

    pub fn get_instantiation_count(&self, code_id: u128) -> u128 {
        match self.instantiation_count.lock().unwrap().get(&code_id) {
            Some(count) => *count,
            None => 0,
        }
    }

    /// Saves a SC code. Uses the Symb Engine to produce a RWS profile
    /// for the contract and saves the profile information for this contract.
    /// Sets instantiation count for this new SC code to 1
    pub fn save(&mut self, sc_code: &[u8]) -> std::io::Result<u128> {
        let curr_dir = std::env::current_dir()?;
        let rel_path = curr_dir.join(contract_path(self.sc_code_id));
        let mut file_writer = File::create(rel_path)?;
        file_writer.write_all(sc_code)?;

        let se_profile = SEEngine::parse_smart_contract(sc_code);
        let sc_profile = SCProfileParser::from_se_profile(se_profile);

        self.profiles.insert(self.sc_code_id, Arc::new(sc_profile));
        
        self.instantiation_count.lock().unwrap().insert(self.sc_code_id, 0);

        let id = self.sc_code_id;
   
        self.sc_code_id += 1;
        
        Ok(id)
    }

    pub fn get_code(&self, code_id: u128) -> std::io::Result<Vec<u8>> {
        let curr_dir = std::env::current_dir()?;
        let rel_path = curr_dir.join(contract_path(code_id));
        let mut f = File::open(rel_path)?;
        let mut code: Vec<u8> = vec![];
        f.read_to_end(&mut code)?;
        Ok(code)
    }

    fn get_profile(&self, code_id: u128) -> Result<Arc<SCProfile>, String> {
        match self.profiles.get(&code_id) {
            Some(profile) => Ok(Arc::clone(profile)),
            None => Err("Profile doesn't exist".to_string()) 
        }
    }

    fn cleanup(&mut self) {
        for id in 0..self.sc_code_id {
            fs::remove_file(contract_path(id)).unwrap();
        }
    } 
}




#[derive(Clone)]
pub struct PersistentBackend<A, S, Q> 
where
    A: BackendApi, 
    S: PartitionedStorage, 
    Q: Querier
{
    pub api: Arc<A>,
    /// The lock is always used as read, unless when we start the block execution.
    /// That is the only time we lock as write, to partition the items at the start of the block,
    /// Only 1 thread does this
    pub storage: Arc<S>,
    pub querier: Arc<RwLock<Q>>,
}

struct SCInstance<A, S, Q> 
where
    A: BackendApi, 
    S: PartitionedStorage, 
    Q: Querier
{
    sc_code_id: u128,
    compiled_code: Arc<Module>,
    state: Arc<PersistentBackend<A, S, Q>>
}

impl<A, S, Q> SCInstance<A, S, Q> 
where
    A: BackendApi, 
    S: PartitionedStorage, 
    Q: Querier
{
    fn new(sc_code_id: u128, compiled_code: Arc<Module>, state: Arc<PersistentBackend<A, S, Q>>) -> Self {
        Self {
            sc_code_id,
            compiled_code,
            state
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
    S: PartitionedStorage, 
    Q: Querier
{
    pub state: Arc<PersistentBackend<A, S, Q>>,
    pub compiled_code: Arc<Module>,
}

/// Stores the SC's state, compiled module and code_id
/// for each instantiated contract.
//                 SC address -> SC instantiation
type SCStorage<A, S, Q> = DashMap<String, Arc<SCInstance<A, S, Q>>>;

/// Mocks interface for handling smart contracts.
/// 
/// This includes both static state - SC code & profile, as well as
/// "dynamic state" - SC state per each instantiation of a contract & its 
/// corresponding compiled wasm module. 
pub struct SCManager<A, S, Q> 
where
    A: BackendApi + 'static,
    S: PartitionedStorage + 'static,
    Q: Querier + 'static
{
    static_data: Arc<RwLock<SCStaticData>>,
    sc_storage: SCStorage<A, S, Q>,
}

impl<A, S, Q> SCManager<A, S, Q> 
where
    A: BackendApi, 
    S: PartitionedStorage, 
    Q: Querier
{
    pub fn new() -> SCManager<A, S, Q> {
        SCManager {
            static_data: Arc::new(RwLock::new(SCStaticData::new())),
            sc_storage: DashMap::new(),
        }
    }

    /// Partitions storage items given the keys and the SC address.
    /// Note that the storage for some contract may not yet exist. For such cases, we 
    /// ignore partitioning, and only partition for existing storages
    pub fn partition_storage(&self, contract_keys: Vec<ContractRWS>) {
        for contract in contract_keys {
            match self.sc_storage.get(&contract.address) {
                Some(mut storage) => {
                    storage.state.storage
                    .partition_items(contract.rws);
                },

                None => continue
            }
        }
    }

    /// Sums up all partitions and stores the item as a single partition.
    /// See the comment on above function about the use of a match when gettin gthe storage
    pub fn sum_partitions(&self, contract_keys: Vec<ContractRWS>) {
        for contract in contract_keys {
            match self.sc_storage.get(&contract.address) {
                Some(mut storage) => 
                    storage.state.storage
                    .sum_partitioned_items(contract.rws),

                None => continue
            }
        }
    }

    /// Saves the storage & compiled module that refers to some instantiated SC
    pub fn save_instance(&self, address: String, code_id: u128,
        compiled_code: Arc<Module>, state: Arc<PersistentBackend<A, S, Q>>) {
        self.sc_storage.insert(address.clone(), Arc::new(
            SCInstance::new(
                code_id,
                compiled_code, 
                state)
            ));
        self.static_data.write().unwrap().incr_instantiation(code_id);
    }

    pub fn get_instance_data(&self, address: &String) -> Option<InstanceData<A, S, Q>> {
        match self.sc_storage.get(address) {
            Some(sc_instance) => Some(InstanceData {
                compiled_code: Arc::clone(&sc_instance.compiled_code),
                state:         Arc::clone(&sc_instance.state),
            }),
            None => None
        }

    }

    pub fn get_code(&self, code_id: u128) -> std::io::Result<Vec<u8>> {
        self.static_data.read().unwrap().get_code(code_id)
    }

    /// Saves SC code in Filsystem & builds the respective Symb. Exec.
    /// tree for the contract
    pub fn save_code(&self, code: &[u8]) -> std::io::Result<()> {
        self.static_data.write().unwrap().save(code)?;
        Ok(())
    }

    pub fn get_instantiation_count(&self, code_id: u128) -> u128 {
        self.static_data.read().unwrap().get_instantiation_count(code_id)
    }

    pub fn get_profile(&self, code_id: u128) -> Arc<SCProfile> {
        self.static_data.read().unwrap().get_profile(code_id).unwrap()
    }

    pub fn cleanup(&self) {
        self.static_data.write().unwrap().cleanup();
    }
}





#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use cosmwasm_std::{ContractResult, Empty, Response};
    use serial_test::serial;
    use wasmer::Store;

    use crate::{call_instantiate, 
        internals::instance_from_module, 
        symb_exec::{EntryPoint, SEStatus}, testing::{mock_env, mock_info, mock_persistent_backend, MockApi, MockQuerier, MockStoragePartitioned, MockStorageWrapper}, 
        wasm_backend::{compile, make_compiling_engine, make_runtime_engine}, 
        InstanceOptions, Size};

    use super::*;

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");
    const HIGH_GAS_LIMIT: u64 = 20_000_000_000_000; // ~20s, allows many calls on one instance
    const DEFAULT_MEMORY_LIMIT: Size = Size::mebi(64);


    #[test]
    #[serial]
    fn generics_test() {
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        let module = Arc::new(compile( &engine, CONTRACT).unwrap());
        let partitioned_store = Arc::new(MockStoragePartitioned::default());
        let backend = Arc::new(mock_persistent_backend(&[], partitioned_store));
        SCInstance::new(0, Arc::clone(&module), Arc::clone(&backend));

        let sc_manager = Arc::new(RwLock::new(SCManager::new()));
        sc_manager.write().unwrap().save_instance(String::from("a"), 0, module, backend);

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

        sc_static_data.save(contract.as_slice()).unwrap();

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

    // #[ignore]
    #[test]
    #[serial]
    fn sc_manager_workflow() {
        let sc_manager = SCManager::new();
        // save code
        sc_manager.save_code(CONTRACT).unwrap();
        // get code
        let code = sc_manager.get_code(0).unwrap();


        // compile code & create storage
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        let module = compile( &engine, code.as_slice()).unwrap();
        let partitioned_storage = Arc::new(MockStoragePartitioned::default());
        let mock_backend = Arc::new(mock_persistent_backend(&[], partitioned_storage));

        // save it to that SC code
        sc_manager.save_instance(
            "a".to_owned(), 
            0, 
            Arc::new(module), 
            Arc::clone(&mock_backend)
        );

        // get instance data
        let instance_data = sc_manager.get_instance_data(&"a".to_owned()).unwrap();

        // instantiate vm
        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT, };
        let engine = make_runtime_engine(Some(DEFAULT_MEMORY_LIMIT));
        let store = Store::new(engine);

        let rws = vec![];
        let partitioned_items = HashSet::new();
        let address = String::from('a');
        
        let concurrent_backend = ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(
            mock_backend, address, rws, Arc::new(partitioned_items));

        let mut instance = instance_from_module(
            store, 
            &*instance_data.compiled_code, 
            concurrent_backend, 
            much_gas.gas_limit, 
            None).unwrap();

        // execute instantiate contract
        let msg = br#"{}"#;
        let contract_res = call_instantiate::<_, _, _, Empty>(
            &mut instance, 
            &mock_env(), 
            &mock_info("", &[]), 
            msg
        ).unwrap();
        
        assert_eq!(contract_res, ContractResult::Ok(Response::new()));
        assert_eq!(sc_manager.get_instantiation_count(0), 1);

        sc_manager.cleanup();

    }

    #[test]
    #[serial]
    fn partition_storage() {
        let sc_manager = SCManager::new();
        // save code
        sc_manager.save_code(CONTRACT).unwrap();

        // compile code & create storage
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        let module = compile( &engine, CONTRACT).unwrap();
        let partitioned_storage = Arc::new(MockStoragePartitioned::default());
        let mock_backend = Arc::new(mock_persistent_backend(&[], partitioned_storage));

        // save it to that SC code
        sc_manager.save_instance(
            "a".to_owned(), 
            0, 
            Arc::new(module), 
            mock_backend
        );

        // get instance data
        let instance_data = sc_manager.get_instance_data(&"a".to_owned()).unwrap();

        // instantiate vm
        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT, };
        let engine = make_runtime_engine(Some(DEFAULT_MEMORY_LIMIT));
        let store = Store::new(engine);

        let rws = vec![];
        let partitioned_items = HashSet::new();
        let concurrent_backend = ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(
            instance_data.state, String::from(""), rws, Arc::new(partitioned_items));

        let mut instance = instance_from_module(
            store, 
            &*instance_data.compiled_code, 
            concurrent_backend, 
            much_gas.gas_limit, 
            None).unwrap();

        // execute instantiate contract to create an item in storage
        let msg = br#"{}"#;
        call_instantiate::<_, _, _, Empty>(
            &mut instance, 
            &mock_env(), 
            &mock_info("", &[]), 
            msg
        ).unwrap();

        let key_written = vec![0, 4, 98, 97, 110, 107, 65, 68, 77, 73, 78];

        sc_manager.partition_storage(vec![ContractRWS {
            address: "a".to_owned(),
            rws: vec![key_written.clone()]
        }]);

        let instance = sc_manager.get_instance_data(&"a".to_owned()).unwrap();
        let storage = &(*instance.state.storage) as *const MockStoragePartitioned;
        let item = unsafe { (*storage).get_item(&key_written) };

    }

}