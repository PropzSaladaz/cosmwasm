use std::{collections::{HashMap, HashSet}, sync::{Arc, RwLock}};

use cosmwasm_std::{Api, CustomQuery, Empty, QuerierWrapper};
use wasmer::Store;

use crate::{
    backend::ConcurrentBackend, call_execute, call_instantiate, call_query, 
    internals::instance_from_module, 
    symb_exec::{Key, ReadWrite, SEStatus, TransactionDependency, TxRWS, WriteType}, 
    testing::{mock_env, mock_info, MockApi, MockQuerier, MockStorageWrapper, PartitionedStorage}, 
    vm_manager::ContractRWS, 
    wasm_backend::{compile, make_compiling_engine, make_runtime_engine}, 
    BackendApi, InstanceOptions, Querier, Size, Storage
};

use super::sc_storage::{PersistentBackend, SCManager};

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
        sender_address: String
    },
    Invocation {
        message: &'a [u8],
        entry_point: InstantiatedEntryPoint,
        sender_address: String,
        contract_address: String,
        code_id: u128,
    },
}

pub enum InstantiatedEntryPoint {
    Execute,
    Query,
    Reply
}


type Counter = i32;
pub type Block<'a> = Vec<VMMessage<'a>>;

/// mapping (code_id, nth_instantiation) => address
pub type AddressMapper = dyn Fn(u128, u128) -> String;
pub type BackendBuilder<A, S, Q> = dyn Fn(Arc<S>) -> PersistentBackend<A, S, Q>;

/// Stateful manager used to instantiate VMs for contract execution,
/// passing them a reference to its corresponding persistent storage
pub struct VMManager<A, S, Q>
where
    A: BackendApi + 'static,
    S: PartitionedStorage + 'static,
    Q: Querier + 'static,
{
    state_manager: Arc<RwLock<SCManager<A, S, Q>>>,

    /// RWS per message, following the order of messages in the block
    rws: Vec<RWSContext>,

    /// Storage keys that are partitioned, by SC address
    /// These keys will be passed to the ConcurrentBackend, when executing,
    /// just before creating the instance, so that it has knowledge of which items
    /// were partitioned when handling storage gets/sets
    /// May be shared across threads - thus the Arc
    partitioned_items_per_sc: HashMap<String, Arc::<HashSet<Vec<u8>>>>,

    /// will be computed when blockchain is replayed, & when we instantiate contracts, etc we
    /// will use the addresses from the replay
    address_mapper: Box<AddressMapper>,

    storage_partitions: u8,
    
    backend_builder: Box<BackendBuilder<A, S, Q>>, 
}


/// This is a read-only version of depsMut -> we won't change anything
/// in it when parsing the RWS, thus storage can be a immutable reference
pub struct DepsMut<'a, C: CustomQuery = Empty> {
    pub storage: &'a dyn cosmwasm_std::Storage,
    pub api: &'a dyn Api,
    pub querier: QuerierWrapper<'a, C>,
}

enum RWS {
    ReadWrite(TxRWS),
    Bytes(Vec<Vec<u8>>)
}

/// Used before apllying the algorithm that identifies the keys to partition.
/// This struct is used only to store temporarily the RWS and the profile completeness gotten
/// from using the message inputs
#[derive(Debug, PartialEq)]
struct RWSContext {
    rws: TxRWS,
    address: String, 
}

impl<A, S, Q> VMManager<A, S, Q> 
where
    A: BackendApi, 
    S: PartitionedStorage, 
    Q: Querier
{

    pub fn new(state_manager: Arc<RwLock<SCManager<A, S, Q>>>, address_mapper: Box<AddressMapper>, storage_partitions: u8,
        backend_builder: Box<BackendBuilder<A, S, Q>>) -> Self
    {
        VMManager {
            state_manager,
            rws: vec![],
            partitioned_items_per_sc: HashMap::new(),
            address_mapper,
            storage_partitions,
            backend_builder
        }
    }

    /// Given a block of messages, fetch the RWS for each individual tx - this is done using information from the
    /// contract inputs and the already built SE profile when the SC was installed.
    /// 
    /// Then partitions a set of storage items according to the operation type (Commutative vs. Non commutative)
    /// and executes the block.
    /// Finally sums all partitions.
    pub fn handle_block(&mut self, block: Block) -> std::io::Result<Vec<String>> {
        let rws = self.get_rws(&block);
        let partitioned_keys = self.partition_storage(&rws);
        // save all partitioned items
        for sc in partitioned_keys.clone() {
            let mut set = HashSet::new();
            for item in sc.rws {
                set.insert(item);
            }
            self.partitioned_items_per_sc.entry(sc.address).or_insert(Arc::new(set));
        }
        let resps = self.execute_block(block, rws).unwrap();
        self.sum_partitions(partitioned_keys);

        Ok(resps)
    }


    /// Determine which RWS are suitable for partitioning at the storage level, and partition those.
    /// Return the partitioned items' keys.
    fn partition_storage(&mut self, rws: &Vec<RWSContext>) -> Vec<ContractRWS> {
        let keys = self.decide_keys_to_partition(rws, 3);
        self.state_manager.read().unwrap().partition_storage(keys.clone());
        keys
    }

    /// Sums up all partitioned items at the start of the block, and converts them into
    /// single items.
    fn sum_partitions(&mut self, contract_keys: Vec<ContractRWS>) {
        self.state_manager.read().unwrap().sum_partitions(contract_keys)
    }

    /// Get the RWS given an input message for some contract.
    /// Fetches the SE profile, parses it & gets the final RWS in form of keys as bytes
    /// It returns a vec where each item contains the contract address as well as all the keys
    /// it will touch
    fn get_rws(&self, block: &Block) -> Vec<RWSContext> {
        let mut rws = vec![];
        for msg in block {
            rws.push(match msg {
                VMMessage::Instantiation { 
                    message, 
                    contract_code_id,
                    sender_address: _
                } => RWSContext {
                        rws: TxRWS { storage_dependency: TransactionDependency::INDEPENDENT, profile_status: SEStatus::Complete, rws: vec![ReadWrite::default()]},
                        address: String::from("")
                 }, // TODO this needs to be implemented!!

                VMMessage::Invocation { 
                    message, 
                    entry_point,
                    sender_address: _, 
                    contract_address, 
                    code_id
                } => {
                    let profile = self.state_manager.read().unwrap().get_profile(*code_id);
                    match &self.state_manager.read().unwrap().get_instance_data(contract_address) {
                        Some(sc_instance) => {
                            // Build mock depsMut
                            let storage = Arc::clone(&sc_instance.state.storage);
                            let querier = cosmwasm_std::testing::MockQuerier::default();
                            let mut_deps = DepsMut { 
                                storage: &*storage,
                                api: &cosmwasm_std::testing::MockApi::default(), 
                                querier: cosmwasm_std::QuerierWrapper::new( &querier)
                            };
                            match entry_point {
                                InstantiatedEntryPoint::Execute => RWSContext {
                                    rws: profile.get_rws_execute(&mut_deps, &mock_env(), &mock_info("", &[]), message),
                                    address: contract_address.clone()
                                },
                                InstantiatedEntryPoint::Query   => RWSContext {
                                    rws: profile.get_rws_query(&mut_deps, &mock_env(), &mock_info("", &[]), message),
                                    address: contract_address.clone(),
                                },
                                InstantiatedEntryPoint::Reply => todo!(),
                            }
                        }
                        // If invocation on a contract that wasn't yet instantiated --> Do not partition anything
                        None => continue
                    }
                }
            });
        };
        rws
    }


    /// Given the RWS of each contract, identify write-incremental-intensive keys suitable for partitioning.
    /// For each write, check if it is incremental, i.e, sums/subtracts some value
    /// over its previous one (reads the key it will write into).
    /// 
    /// For each non-incremental read for some key, we will need to read all partitions, thus we discount on
    /// the score for that key.
    /// 
    /// If a counter has a final positive score, i.e, has more incremental-writes than reads,
    /// then it is suitable to be partitioned.
    /// 
    /// Inputs: RWS for each contract (each RWS has associated the SC address)
    /// return: RWS to be partitioned for each SC
    fn decide_keys_to_partition(&self, rws: &Vec<RWSContext>, partial_full_proportion: Counter) -> Vec<ContractRWS> {
        //                              contract address -> key -> counter
        let mut partial_read_map: HashMap<String, HashMap<Vec<u8>, Counter>> = HashMap::new();
        let mut rws_per_contract: HashMap<String, ContractRWS> = HashMap::new();

        // Running over the stored RWS of each SC
        for contract_context in rws {
            let sc_rws = &contract_context.rws;
            let address = &contract_context.address;

            // TODO - maybe is better, for all RWS to just discount and assume is full read/write
            if sc_rws.profile_status == SEStatus::Incomplete {
                continue;
            }

            // Running over each Read/Write of the current RWS for the current contract
            for read_write in &sc_rws.rws {
                match read_write {
                    ReadWrite::Read{
                        storage_dependency: _,
                        key: Key::Bytes(key_bytes),
                        commutativity
                    } => {
                        // create (if needed) tmp mapping of some SC keys into their counters
                        let contract_partial_map = partial_read_map.entry(address.clone()).or_insert(HashMap::new());
                        
                        match commutativity {
                            WriteType::NonCommutative => {
                                // update the counters of current SC
                                contract_partial_map.entry(key_bytes.clone())
                                    .and_modify(|c| *c -= partial_full_proportion)
                                    .or_insert(-partial_full_proportion);
                            },
                            // TODO - rethink if commutative reads influence the algo or not
                            _ => ()
                        };

                        // create (if needed) tmp sc storage storing the SC address (needed later to fetch the storage)
                        rws_per_contract.entry(address.clone()).or_insert(ContractRWS {
                            rws: vec![],
                            address: address.clone()
                        });
                    },
                    ReadWrite::Write { 
                        storage_dependency: _,
                        key: Key::Bytes(key_bytes), 
                        commutativity 
                    } => {
                        // create (if needed) tmp mapping of some SC keys into their counters
                        let contract_partial_map = partial_read_map.entry(address.clone()).or_insert(HashMap::new());

                        // create (if needed) tmp sc storage storing the SC address (needed later to fetch the storage)
                        rws_per_contract.entry(address.clone()).or_insert(ContractRWS {
                            rws: vec![],
                            address: address.clone()
                        });

                        // TODO is there a more efficient way instead of using key_bytes.clone() ?
                        match commutativity {
                            WriteType::Commutative    => contract_partial_map.entry(key_bytes.clone())
                                .and_modify(|c| *c += 1)
                                .or_insert(1),

                            WriteType::NonCommutative => contract_partial_map.entry(key_bytes.clone())
                                .and_modify(|c| *c -= partial_full_proportion)
                                .or_insert(-partial_full_proportion)
                        };
                    },
                    other => unreachable!("RWS should output the key as bytes. Got {:?}", other)
                };
            }
        }

        // Convert the keys of each contract into a RWS for each contract
        for (address, sc_counters) in partial_read_map.into_iter() {
            let contract_rws = rws_per_contract.get_mut(&address).unwrap();
            for (key, counter) in sc_counters.into_iter() {
                println!("{:?} - {:?}", key, counter);
                if counter > 0 {
                    contract_rws.rws.push(key);
                }
            }
        }

        return rws_per_contract.into_values().collect();

    }

    fn execute_block(&mut self, block: Block, rws: Vec<RWSContext>) -> std::io::Result<Vec<String>> {
        let mut resps = vec![];
        for (msg, rws) in block.into_iter().zip(rws) {
            let rws = rws.rws.rws;
            resps.push(match msg {
                // TODO - check efficiency of cloning rws. Maybe we can pass just references (need to specify lifetimes)
                VMMessage::Instantiation { 
                    message, 
                    contract_code_id,
                    sender_address
                } => self.compile_instantiate_vm(contract_code_id, message, sender_address, rws).unwrap(),

                VMMessage::Invocation { 
                    message, 
                    entry_point,
                    sender_address, 
                    contract_address, 
                    code_id
                } => {
                        // receiving a message from a contract that has no partitioned items
                        let mut partitioned_items = &Arc::new(HashSet::new()); 
                        if let Some(part) = self.partitioned_items_per_sc.get(&contract_address) {
                            partitioned_items = part;
                        }
                        match entry_point {
                            InstantiatedEntryPoint::Execute => self.instantiate_vm(code_id, &contract_address, message, sender_address, 
                                rws, Arc::clone(partitioned_items), VMCall::Execute ).unwrap(),
                            InstantiatedEntryPoint::Query   => self.instantiate_vm(code_id, &contract_address, message, sender_address, 
                                rws, Arc::clone(partitioned_items), VMCall::Query   ).unwrap(),
                            InstantiatedEntryPoint::Reply => String::from(""),
                    } 
                }
            });
        }
        Ok(resps)
    }

    /// Used on contract instantiations to compile the code
    fn compile_instantiate_vm(&self, contract_code_id: u128, msg: &[u8], sender_address: String, rws: Vec<ReadWrite>) -> std::io::Result<String> {
        // Create the compiled module
        let code = self.state_manager.read().unwrap().get_code(contract_code_id)?;
        let engine = Box::new(make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT)));
        let module = Arc::new(compile( &engine, code.as_slice()).unwrap());
        let partitioned_storage = Arc::new(S::new(self.storage_partitions));
        let backend = Arc::new((self.backend_builder)(partitioned_storage));
        
        // get deterministic address
        let address = (self.address_mapper)(
            contract_code_id, 
            self.state_manager.read().unwrap().get_instantiation_count(contract_code_id)
        );

        // save instance
        self.state_manager.read().unwrap().save_instance(
            address.clone(), 
            contract_code_id, 
            module, 
            Arc::clone(&backend));

        // build runtime intformation to execute
        let instance_data = self.state_manager.read().unwrap().get_instance_data(&address).unwrap();
        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
        let engine = make_runtime_engine(Some(DEFAULT_MEMORY_LIMIT));
        let store = Store::new(engine);
        
        // For Instantiation calls we don't yet have the SC address, thus we can't know if it has or not partitioned items.
        // Also, there is only 1 instantiation for some SC, so it doesnt make much sense to partition since there will be only 1 call
        // Thus the HashSet::new() -> no partitioned items
        let partitioned_items = HashSet::new();
        let concurrent_backend = ConcurrentBackend::<A, MockStorageWrapper, Q>::new(
            instance_data.state, sender_address, rws, Arc::new(partitioned_items));

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
    fn instantiate_vm(&self, code_id: u128, contract_address: &String, message: &[u8], sender_address: String, 
        rws: Vec<ReadWrite>, partitioned_items: Arc<HashSet<Vec<u8>>>, call_type: VMCall) -> std::io::Result<String> {
        let instance_data = self.state_manager.read().unwrap().get_instance_data(&contract_address).unwrap();

        let code = self.state_manager.read().unwrap().get_code(code_id)?;
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        let module = Arc::new(Box::new(compile( &engine, code.as_slice()).unwrap()));
        let store = Store::new(engine);

        let concurrent_backend = ConcurrentBackend::<A, MockStorageWrapper, Q>::new(
            instance_data.state, sender_address, rws, partitioned_items);

        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
        let mut instance = instance_from_module(
            store, 
            &module, 
            concurrent_backend,
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
    use std::{collections::{HashMap, HashSet}, sync::{Arc, RwLock}};

    use cosmwasm_std::{ContractResult, Empty, Response};
    use serial_test::serial;
    use wasmer::Store;

    use crate::{
        backend::ConcurrentBackend, call_instantiate, internals::instance_from_module, symb_exec::{Key, ReadWrite, TransactionDependency, TxRWS, WriteType}, testing::{mock_env, mock_info, mock_persistent_backend, MockApi, MockQuerier, MockStoragePartitioned, MockStorageWrapper}, vm_manager::vm_manager::{RWSContext, VMCall, DEFAULT_MEMORY_LIMIT, HIGH_GAS_LIMIT}, wasm_backend::{compile, make_compiling_engine, make_runtime_engine}, InstanceOptions, InstantiatedEntryPoint, SCManager, SEStatus, VMMessage
    };

    use super::{AddressMapper, BackendBuilder, VMManager};

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");


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

    fn mock_vm_manager() -> VMManager<MockApi, MockStoragePartitioned, MockQuerier> {
        let state_manager: SCManager<MockApi, MockStoragePartitioned, MockQuerier> = SCManager::new();
        // simulate installing a contract
        state_manager.save_code(CONTRACT).unwrap();

        let state_manager = Arc::new(RwLock::new(state_manager));
        VMManager::new(
            Arc::clone(&state_manager), 
            mock_address_mapper(),
            2,
            mock_backend_builder(),
        )
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
            2,
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
        let partitioned_storage = Arc::new(MockStoragePartitioned::default());
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
        let partitioned_items = HashSet::new();
        let concurrent_backend = ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(
            instance.state, String::from(""), rws, Arc::new(partitioned_items));

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
        println!("{:#?}", contract_res);

        assert_eq!(contract_res.unwrap(), ContractResult::Ok(Response::new()));
        assert_eq!(state_manager.get_instantiation_count(0), 1);

        state_manager.cleanup();
    }

    #[test]
    #[serial]
    fn instantiate_vm() {
        let vm_manager = mock_vm_manager();

        let msg = br#"{}"#;
        let resp = vm_manager.compile_instantiate_vm(0, msg, String::from(""), vec![]).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        vm_manager.state_manager.read().unwrap().cleanup();
    }

    #[test]
    #[serial]
    fn execute_vm() {
        let vm_manager = mock_vm_manager();

        let msg = br#"{}"#;
        let resp = vm_manager.compile_instantiate_vm(0, msg, String::from(""), vec![]).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        let msg = br#"{
            "AddOne": {}
        }"#;
        let resp = vm_manager.instantiate_vm(0, &String::from("a"), msg, String::from(""), vec![], Arc::new(HashSet::new()), VMCall::Execute).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);
        vm_manager.state_manager.read().unwrap().cleanup();
    }

    #[test]
    #[serial]
    fn query_vm() {
        let vm_manager = mock_vm_manager();

        let msg = br#"{}"#;
        let resp = vm_manager.compile_instantiate_vm(0, msg,  String::from(""), vec![]).unwrap();
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resp);

        let msg = br#"{
            "GetBalance": {}
        }"#;
        let resp = vm_manager.instantiate_vm(0, &String::from("a"), msg,  String::from(""), vec![], Arc::new(HashSet::new()), VMCall::Query).unwrap();
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
                message: br#"{}"#,
                sender_address: String::from(""),
            },
            // VMMessage::Invocation {
            //     entry_point: InstantiatedEntryPoint::Query,
            //     contract_address: "a".to_owned(),
            //     message: br#"{
            //         "GetBalance": {}
            //     }"#,
            //     code_id: 0,
            //     sender_address: String::from(""),
            // },
            // VMMessage::Invocation {
            //     entry_point: InstantiatedEntryPoint::Execute,
            //     contract_address: "a".to_owned(),
            //     message: br#"{
            //         "AddOne": {}
            //     }"#,
            //     code_id: 0,
            //     sender_address: String::from(""),
            // },
            // VMMessage::Invocation {
            //     entry_point: InstantiatedEntryPoint::Query,
            //     contract_address: "a".to_owned(),
            //     message: br#"{
            //         "GetBalance": {}
            //     }"#,
            //     code_id: 0,
            //     sender_address: String::from(""),
            // },
            // VMMessage::Invocation {
            //     entry_point: InstantiatedEntryPoint::Execute,
            //     contract_address: "a".to_owned(),
            //     message: br#"{
            //         "AddUser": {
            //             "admin": "Balelas"
            //         }
            //     }"#,
            //     code_id: 0,
            //     sender_address: String::from(""),
            // },
            // VMMessage::Instantiation {
            //     contract_code_id: 0,
            //     message: br#"{}"#,
            //     sender_address: String::from(""),
            // },
            // VMMessage::Invocation {
            //     entry_point: InstantiatedEntryPoint::Execute,
            //     contract_address: "b".to_owned(),
            //     message: br#"{
            //         "AddOne": {}
            //     }"#,
            //     code_id: 0,
            //     sender_address: String::from(""),
            // },
            // VMMessage::Invocation {
            //     entry_point: InstantiatedEntryPoint::Execute,
            //     contract_address: "a".to_owned(),
            //     message: br#"{
            //         "AddOne": {}
            //     }"#,
            //     code_id: 0,
            //     sender_address: String::from(""),
            // },
            // VMMessage::Invocation {
            //     entry_point: InstantiatedEntryPoint::Query,
            //     contract_address: "a".to_owned(),
            //     message: br#"{
            //         "GetBalance": {}
            //     }"#,
            //     code_id: 0,
            //     sender_address: String::from(""),
            // },
            // VMMessage::Invocation {
            //     entry_point: InstantiatedEntryPoint::Query,
            //     contract_address: "b".to_owned(),
            //     message: br#"{
            //         "GetBalance": {}
            //     }"#,
            //     code_id: 0,
            //     sender_address: String::from(""),
            // },
        ];

        let resps = vm_manager.handle_block(msgs).unwrap();
        
        assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[0]);
        // assert_eq!("{\"balance\":1000}", resps[1]);
        // assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[2]);
        // assert_eq!("{\"balance\":1001}", resps[3]);
        // assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[4]);
        // assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[5]);
        // assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[6]);
        // assert_eq!("Ok(Response { messages: [], attributes: [], events: [], data: None })", resps[7]);
        // assert_eq!("{\"balance\":1002}", resps[8]);
        // assert_eq!("{\"balance\":1001}", resps[9]);

        vm_manager.state_manager.read().unwrap().cleanup();

    }


    #[test]
    #[serial]
    fn get_rws() {
        let mut vm_manager = mock_vm_manager();

        let msgs = vec![
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#,
                sender_address: String::from(""),
            },
        ];

        // instantiate first, to create storage
        vm_manager.handle_block(msgs).unwrap();

        // only after having storage created
        let msgs = vec![
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "a".to_owned(),
                message: br#"{
                    "AddOne": {}
                }"#,
                code_id: 0,
                sender_address: String::from(""),
            },
        ];

        let rws = vm_manager.get_rws(&msgs);
        assert_eq!(
            rws,
            vec![RWSContext {
                address: "a".to_owned(),
                rws: TxRWS {
                    storage_dependency: TransactionDependency::INDEPENDENT,
                    profile_status: SEStatus::Complete,
                    rws: vec![
                        ReadWrite::Read {
                            storage_dependency: TransactionDependency::INDEPENDENT,
                            key: Key::Bytes(vec![0, 4, 98, 97, 110, 107, 65, 68, 77, 73, 78]),
                            commutativity: WriteType::Commutative,
                        },
                        ReadWrite::Write {
                            storage_dependency: TransactionDependency::INDEPENDENT,
                            key: Key::Bytes(vec![0, 4, 98, 97, 110, 107, 65, 68, 77, 73, 78]),
                            commutativity: WriteType::Commutative
                        },
                    ]
                }
            }]
        );
        println!("{:#?}", rws);
        
        vm_manager.state_manager.read().unwrap().cleanup();
    }

    #[test]
    #[serial]
    fn decide_keys_to_partition() {
        let mut vm_manager = mock_vm_manager();
        
        let key_a = vec![1];
        let key_b = vec![2];
        let key_c = vec![3];
        let key_d = vec![4];

        // Testing the following RWS:
        // Tx1:
        //    - W(A): R(A) + R(B) + 1
        //    - W(B): R(B) + 3
        //    - W(C): R(C) - 2
        // Tx2:
        //    - W(D): R(D) + 3
        //    - W(A): R(A) * 2
        //    - W(B): R(B) + 1 + R(A)
        // Tx3:
        //    - W(A): R(A) + 1
        //    - W(B): R(B) + 1
        // Tx4:
        //    - W(C): R(A) + 2
        //    - W(B): R(B) + 3
        let partition_keys = vm_manager.decide_keys_to_partition(&vec![
            // Tx1
            RWSContext {
                address: "a".to_owned(),
                rws: TxRWS { 
                    storage_dependency: TransactionDependency::INDEPENDENT,
                    profile_status: SEStatus::Complete, 
                    rws: vec![
                        // R(A) from write below
                        ReadWrite::Read { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_a.clone()), commutativity: WriteType::Commutative },
                        // R(B) from write below
                        ReadWrite::Read { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_b.clone()), commutativity: WriteType::NonCommutative },
                        // W(A): R(A) + R(B) + 1
                        ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_a.clone()), commutativity: WriteType::Commutative },

                        // W(B): R(B) + 3
                        ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_b.clone()), commutativity: WriteType::Commutative },
                        // W(C): R(C) - 2
                        ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_c.clone()), commutativity: WriteType::Commutative }
                    ] 
                }
            },
            // Tx2
            RWSContext {
                address: "a".to_owned(),
                rws: TxRWS { 
                    storage_dependency: TransactionDependency::INDEPENDENT,
                    profile_status: SEStatus::Complete, 
                    rws: vec![
                        // R(D) from write below
                        ReadWrite::Read { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_d.clone()), commutativity: WriteType::Commutative },
                        // W(D): R(D) + 3
                        ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_d.clone()), commutativity: WriteType::Commutative },

                        // R(A) from write below, since is non commutative
                        ReadWrite::Read { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_a.clone()), commutativity: WriteType::NonCommutative },
                        // W(A): R(A) * 2
                        ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_a.clone()), commutativity: WriteType::NonCommutative },
                        
                        // R(A) from write below, since is non commutative
                        ReadWrite::Read { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_a.clone()), commutativity: WriteType::NonCommutative },
                        // R(B) from write below, is commutative
                        ReadWrite::Read { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_b.clone()), commutativity: WriteType::Commutative },
                        // W(B): R(B) + 1 + R(A)
                        ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_b.clone()), commutativity: WriteType::Commutative },
                    ] 
                }
            },
            // Tx3
            RWSContext {
                address: "a".to_owned(),
                rws: TxRWS { 
                    storage_dependency: TransactionDependency::INDEPENDENT,
                    profile_status: SEStatus::Complete, 
                    rws: vec![
                        // W(A): R(A) + 1
                        ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_a.clone()), commutativity: WriteType::Commutative },
                        // W(B): R(B) + 1
                        ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_b.clone()), commutativity: WriteType::Commutative },
                    ] 
                }
            },
            // Tx4
            RWSContext {
                address: "a".to_owned(),
                rws: TxRWS { 
                    storage_dependency: TransactionDependency::INDEPENDENT,
                    profile_status: SEStatus::Complete, 
                    rws: vec![
                        // R(A) from above write
                        ReadWrite::Read { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_a.clone()), commutativity: WriteType::NonCommutative },
                        // W(C): R(A) + 2
                        ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_c.clone()), commutativity: WriteType::NonCommutative },

                        // R(B) from write below
                        ReadWrite::Read { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_b.clone()), commutativity: WriteType::Commutative },
                        // W(B): R(B) + 3
                        ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key_b.clone()), commutativity: WriteType::Commutative },
                    ] 
                }
            },
        ], 3);

        for item in partition_keys {
            for item in item.rws {
                assert!(vec![key_b.clone(), key_d.clone()].contains(&item))
            }
        }
    }
}