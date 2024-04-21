use std::sync::{Arc, RwLock};

use cosmwasm_std::Empty;
use wasmer::Store;

use crate::{
    backend::ConcurrentBackend, call_execute, call_instantiate, call_query, internals::instance_from_module, testing::{
        mock_env, mock_info}, wasm_backend::{
        compile, 
        make_compiling_engine, make_runtime_engine}, BackendApi, InstanceOptions, Querier, Size, Storage
};

use super::sc_storage::SCManager;

const DEFAULT_MEMORY_LIMIT: Size = Size::mebi(64);
const HIGH_GAS_LIMIT: u64 = 20_000_000_000_000_000; // ~20s, allows many calls on one instance


enum VMCall {
    Execute,
    Query,
}

pub enum VMMessage<'a> {
    Instantiation {
        message: &'a [u8],
        contract_code_id: u128,
    },
    Invocation {
        message: &'a [u8],
        entry_point: InstantiatedEntryPoint,
        contract_address: String,
        code_id: u128,
    },
}

pub enum InstantiatedEntryPoint {
    Execute,
    Query,
    Reply
}

pub type Block<'a> = Vec<VMMessage<'a>>;

/// mapping (code_id, nth_instantiation) => address
pub type AddressMapper = dyn Fn(u128, u128) -> String;
pub type StorageBuilder<S> = dyn Fn() -> S;
pub type BackendBuilder<A, S, Q> = dyn Fn(Arc<RwLock<S>>) -> ConcurrentBackend<A, S, Q>;

/// Stateful manager used to instantiate VMs for contract execution,
/// passing them a reference to its corresponding persistent storage
pub struct VMManager<A, S, Q>
where
    A: BackendApi + 'static,
    S: Storage + 'static,
    Q: Querier + 'static,
{
    state_manager: Arc<RwLock<SCManager<A, S, Q>>>,

    /// will be computed when blockchain is replayed, & when we instantiate contracts, etc we
    /// will use the addresses from the replay
    address_mapper: Box<AddressMapper>,
    
    storage_builder: Box<StorageBuilder<S>>,
    backend_builder: Box<BackendBuilder<A, S, Q>>, 
}

impl<A: BackendApi, S: Storage, Q: Querier> VMManager<A, S, Q> {

    pub fn new(state_manager: Arc<RwLock<SCManager<A, S, Q>>>, address_mapper: Box<AddressMapper>,
        storage_builder: Box<StorageBuilder<S>>, backend_builder: Box<BackendBuilder<A, S, Q>>) -> Self
    {
        VMManager {
            state_manager,
            address_mapper,
            storage_builder,
            backend_builder
        }
    }

    fn partition_storage(&mut self, _: &Block) {

    }

    fn sum_partitions(&mut self) {

    }

    pub fn handle_block(&mut self, block: Block) -> std::io::Result<Vec<String>> {
        self.partition_storage(&block);
        let resps = self.execute_block(&block).unwrap();
        self.sum_partitions();

        Ok(resps)
    }

    fn execute_block(&mut self, block: &Block) -> std::io::Result<Vec<String>> {
        let mut resps = vec![];
        for msg in block {
            resps.push(match msg {
                VMMessage::Instantiation { 
                    message, 
                    contract_code_id 
                } => self.compile_instantiate_vm(*contract_code_id, message).unwrap(),

                VMMessage::Invocation { 
                    message, 
                    entry_point, 
                    contract_address, 
                    code_id
                } => match entry_point {
                    InstantiatedEntryPoint::Execute => self.instantiate_vm(*code_id, contract_address, message, VMCall::Execute ).unwrap(),
                    InstantiatedEntryPoint::Query   => self.instantiate_vm(*code_id, contract_address, message, VMCall::Query   ).unwrap(),
                    InstantiatedEntryPoint::Reply => String::from(""),
                }
            });
        }
        Ok(resps)
    }

    /// Used on contract instantiations to compile the code
    fn compile_instantiate_vm(&self, contract_code_id: u128, msg: &[u8]) -> std::io::Result<String> {
        // Create the compiled module
        let code = self.state_manager.read().unwrap().get_code(contract_code_id)?;
        let engine = Box::new(make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT)));
        let module = Arc::new(compile( &engine, code.as_slice()).unwrap());
        let partitioned_storage = Arc::new(RwLock::new((self.storage_builder)()));
        let backend = Arc::new((self.backend_builder)(partitioned_storage));
        
        // save instance
        // get deterministic address
        let address = (self.address_mapper)(
            contract_code_id, 
            self.state_manager.read().unwrap().get_instantiation_count(contract_code_id)
        );

        self.state_manager.read().unwrap().save_instance(
            address.clone(), 
            contract_code_id, 
            module, 
            Arc::clone(&backend));

        let instance_data = self.state_manager.read().unwrap().get_instance_data(&address);
        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
        let engine = make_runtime_engine(Some(DEFAULT_MEMORY_LIMIT));
        let store = Store::new(engine);

        let mut instance = instance_from_module(
            store, 
            &instance_data.compiled_code, 
            &*backend, 
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
    fn instantiate_vm(&self, code_id: u128, contract_address: &String, message: &[u8], call_type: VMCall) -> std::io::Result<String> {
        let instance_data = self.state_manager.read().unwrap().get_instance_data(&contract_address);

        let code = self.state_manager.read().unwrap().get_code(code_id)?;
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        let module = Arc::new(Box::new(compile( &engine, code.as_slice()).unwrap()));
        let store = Store::new(engine);

        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
        let mut instance = instance_from_module(
            store, 
            &module, 
            &*instance_data.state,
            much_gas.gas_limit,
            None).unwrap();

        Ok(match call_type {
            VMCall::Execute => {
                println!("calling execute for contract: {:?}", contract_address);
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
    use wasmer::Store;

    use crate::{
        call_instantiate, 
        internals::instance_from_module, 
        testing::{mock_env, mock_info, mock_persistent_backend, MockApi, MockQuerier, MockStoragePartitioned}, 
        vm_manager::vm_manager::{VMCall, DEFAULT_MEMORY_LIMIT, HIGH_GAS_LIMIT}, 
        wasm_backend::{compile, make_compiling_engine, make_runtime_engine}, 
        InstanceOptions, InstantiatedEntryPoint, SCManager, VMMessage
    };

    use super::{AddressMapper, BackendBuilder, StorageBuilder, VMManager};

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");

    fn mock_storage_builder() -> Box<StorageBuilder<MockStoragePartitioned>> {
        Box::new(|| {
            MockStoragePartitioned::default()
        })
    }

    fn mock_backend_builder() -> Box<BackendBuilder<MockApi, MockStoragePartitioned, MockQuerier>> {
        Box::new(|storage| {
            mock_persistent_backend(&[], storage)
        })
    }

    fn mock_address_mapper() -> Box<AddressMapper> {
        let mut mapping: HashMap<u128, HashMap<u128, String>> = HashMap::from([(0, HashMap::new())]);
        mapping.get_mut(&0).unwrap().insert(0, "a".to_owned());
        mapping.get_mut(&0).unwrap().insert(1, "b".to_owned());

        Box::new(move |contract_code_id: u128, instantiation: u128| {
            mapping.get(&contract_code_id).unwrap().get(&instantiation).unwrap().clone()
        })
    }

    #[test]
    fn address_mapper() {
        let state_manager: SCManager<MockApi, MockStoragePartitioned, MockQuerier> = SCManager::new();
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
            Box::new(address_mapper),
            mock_storage_builder(),
            mock_backend_builder(),
        );

        assert_eq!((vm_manager.address_mapper)(0, 0), "a");
        assert_eq!((vm_manager.address_mapper)(0, 1), "b");
        assert_eq!((vm_manager.address_mapper)(1, 0), "c");
        assert_eq!((vm_manager.address_mapper)(1, 1), "d");
    }

    #[test]
    fn vanilla_instantiation() {
        // save initial code -> will have code_id = 0
        let state_manager = SCManager::new();
        state_manager.save_code(CONTRACT).unwrap();

        assert_eq!(state_manager.get_code(0).unwrap(), CONTRACT);
        
        // Create the compiled module & storage
        let code = state_manager.get_code(0).unwrap();
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        let module = compile( &engine, code.as_slice()).unwrap();
        let partitioned_storage = Arc::new(RwLock::new(MockStoragePartitioned::default()));
        let backend = Arc::new(mock_persistent_backend(&[], partitioned_storage));

        // save instance
        state_manager.save_instance(
            "a".to_owned(),
            0,
            Arc::new(module),
            backend);

        let instance = state_manager.get_instance_data(&"a".to_owned());

        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT, };
        let engine = make_runtime_engine(Some(DEFAULT_MEMORY_LIMIT));
        let store = Store::new(engine);

        let mut instance = instance_from_module(
            store, 
            &instance.compiled_code, 
            &instance.state, 
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
        println!("{:#?}", contract_res);

        assert_eq!(contract_res.unwrap(), ContractResult::Ok(Response::new()));
        assert_eq!(state_manager.get_instantiation_count(0), 1);
    }

    #[test]
    fn instantiate_vm() {
        // save initial code -> will have code_id = 0
        let state_manager: SCManager<MockApi, MockStoragePartitioned, MockQuerier> = SCManager::new();
        state_manager.save_code(CONTRACT).unwrap();

        assert_eq!(state_manager.get_code(0).unwrap(), CONTRACT);

        let state_manager = Arc::new(RwLock::new(state_manager));
        let vm_manager = VMManager::new(
            Arc::clone(&state_manager), 
            mock_address_mapper(),
            mock_storage_builder(),
            mock_backend_builder(),
        );

        let msg = br#"{}"#;
        let resp = vm_manager.compile_instantiate_vm(0, msg).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);
    }

    #[test]
    fn execute_vm() {
        // save initial code -> will have code_id = 0
        let state_manager: SCManager<MockApi, MockStoragePartitioned, MockQuerier> = SCManager::new();
        state_manager.save_code(CONTRACT).unwrap();

        assert_eq!(state_manager.get_code(0).unwrap(), CONTRACT);

        let state_manager = Arc::new(RwLock::new(state_manager));
        let vm_manager = VMManager::new(
            Arc::clone(&state_manager), 
            mock_address_mapper(),
            mock_storage_builder(),
            mock_backend_builder(),
        );

        let msg = br#"{}"#;
        let resp = vm_manager.compile_instantiate_vm(0, msg).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        let msg = br#"{
            "AddOne": {}
        }"#;
        let resp = vm_manager.instantiate_vm(0, &String::from("a"), msg, VMCall::Execute).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);
        
    }

    #[test]
    fn query_vm() {
        // save initial code -> will have code_id = 0
        let state_manager: SCManager<MockApi, MockStoragePartitioned, MockQuerier> = SCManager::new();
        state_manager.save_code(CONTRACT).unwrap();

        assert_eq!(state_manager.get_code(0).unwrap(), CONTRACT);

        let state_manager = Arc::new(RwLock::new(state_manager));
        let vm_manager = VMManager::new(
            Arc::clone(&state_manager), 
            mock_address_mapper(),
            mock_storage_builder(),
            mock_backend_builder(),
        );

        let msg = br#"{}"#;
        let resp = vm_manager.compile_instantiate_vm(0, msg).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        let msg = br#"{
            "GetBalance": {}
        }"#;
        let resp = vm_manager.instantiate_vm(0, &String::from("a"), msg, VMCall::Query).unwrap();
        assert_eq!("{\"balance\":1000}", resp);
        
    }

    #[test]
    fn persistent_calls() {
        let state_manager: SCManager<MockApi, MockStoragePartitioned, MockQuerier> = SCManager::new();
        // simulate installing a contract
        state_manager.save_code(CONTRACT).unwrap();

        let state_manager = Arc::new(RwLock::new(state_manager));
        let mut vm_manager = VMManager::new(
            Arc::clone(&state_manager), 
            mock_address_mapper(),
            mock_storage_builder(),
            mock_backend_builder(),
        );

        let msgs = vec![
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "a".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#,
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "a".to_owned(),
                message: br#"{
                    "AddOne": {}
                }"#,
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "a".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#,
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "a".to_owned(),
                message: br#"{
                    "AddUser": {
                        "admin": "Balelas"
                    }
                }"#,
                code_id: 0,
            },
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "b".to_owned(),
                message: br#"{
                    "AddOne": {}
                }"#,
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "a".to_owned(),
                message: br#"{
                    "AddOne": {}
                }"#,
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "a".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#,
                code_id: 0,
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: "b".to_owned(),
                message: br#"{
                    "GetBalance": {}
                }"#,
                code_id: 0,
            },
        ];

        let resps = vm_manager.handle_block(msgs).unwrap();
        
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[0]);
        assert_eq!("{\"balance\":1000}", resps[1]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[2]);
        assert_eq!("{\"balance\":1001}", resps[3]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[4]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[5]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[6]);
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[7]);
        assert_eq!("{\"balance\":1002}", resps[8]);
        assert_eq!("{\"balance\":1001}", resps[9]);

    }
}