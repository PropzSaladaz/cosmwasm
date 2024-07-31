use std::{collections::HashMap, sync::{Arc, RwLock}, time::Instant};

use cosmwasm_vm::{
    testing::{mock_persistent_backend, MockApi, MockConcurrentStorage, MockQuerier, MockStorageWrapper}, AddressMapper, ConcurrentBackend, ConcurrentSchedule, InstantiatedEntryPoint, Message, MessageHandler, PersistentBackend, ReadWrite, SCManager, ScAddr, TxId, VMManager, VMMessage};

const SC_ADDR_A: ScAddr = *b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const SC_ADDR_B: ScAddr = *b"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const SC_ADDR_C: ScAddr = *b"cccccccccccccccccccccccccccccccc";
const SC_ADDR_D: ScAddr = *b"dddddddddddddddddddddddddddddddd";
const SC_ADDR_E: ScAddr = *b"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
const SC_ADDR_F: ScAddr = *b"ffffffffffffffffffffffffffffffff";
const SC_ADDR_G: ScAddr = *b"gggggggggggggggggggggggggggggggg";
const SC_ADDR_H: ScAddr = *b"hhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhh";
const SC_ADDR_I: ScAddr = *b"iiiiiiiiiiiiiiiiiiiiiiiiiiiiiiii";

const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");

fn run_persistent_vm() {

    let sc_manager: SCManager<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier> = SCManager::new();

    // create mapping (code_id, instantiation) -> address
    let mut mapping: HashMap<u128, HashMap<u128, ScAddr>> = HashMap::from([
        (0, HashMap::new()),
        (1, HashMap::new())
    ]);
    
    mapping.get_mut(&0).unwrap().insert(0, SC_ADDR_A);
    mapping.get_mut(&0).unwrap().insert(1, SC_ADDR_B);
    mapping.get_mut(&0).unwrap().insert(2, SC_ADDR_C);
    mapping.get_mut(&0).unwrap().insert(3, SC_ADDR_D);
    mapping.get_mut(&0).unwrap().insert(4, SC_ADDR_E);
    mapping.get_mut(&0).unwrap().insert(5, SC_ADDR_F);
    mapping.get_mut(&0).unwrap().insert(6, SC_ADDR_G);
    mapping.get_mut(&0).unwrap().insert(7, SC_ADDR_H);
    mapping.get_mut(&0).unwrap().insert(8, SC_ADDR_I);

    let address_mapper = move |contract_code_id: u128, instantiation: u128| {
        mapping
            .get(&contract_code_id).expect(&format!("Contract code id {:?} is not in the apriori mapping", contract_code_id))
            .get(&instantiation).expect(&format!("Instantiation number {:?} is not in the mapping for contract code id {:?}", instantiation, contract_code_id))
            .clone()
    };

    let backend_builder = |storage| {
        mock_persistent_backend(&[], storage)
    };

    let concurrent_backend_builder = |tx_id: TxId, concurrent_schedule: Arc<ConcurrentSchedule>, 
        persistent_backend: Arc<PersistentBackend<MockApi, MockConcurrentStorage, MockQuerier>>, sc_address: &ScAddr, rws: Vec<ReadWrite>| {
        ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(tx_id, concurrent_schedule, persistent_backend, sc_address, rws)
    };

    let sc_manager = Arc::new(RwLock::new(sc_manager));

    let vm_manager = VMManager::new(
        Arc::clone(&sc_manager),
        Arc::new(address_mapper),
        Arc::new(backend_builder),
        Arc::new(concurrent_backend_builder),
    4,
    2);

    // handle messages
    let mut message_handler = MessageHandler::new(
        sc_manager, 
        vm_manager,
        50
    );
    
    let start_time = Instant::now();

    message_handler.handle_messages(vec![
        Message::Deployment { 
            contract_code:  CONTRACT,
        },
        Message::Invocation(
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            }
        ),
        Message::Invocation(
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            }
        ),
        Message::Invocation(
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            }
        ),
        Message::Invocation(
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            }
        ),
        Message::Invocation(
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            }
        ),
        Message::Invocation(
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            }
        ),
        Message::Invocation(
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            }
        ),
        Message::Invocation(
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            }
        ),
        Message::Invocation(
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
            }
        ),


        // B
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_B,
                code_id: 0,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_B,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),

        // H
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_D,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_D,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),

        // A
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "AddUser": {
                        "admin": "Balelas"
                    }
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),


        // F
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_F,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_F,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_F,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_F,
                message: br#"{
                    "AddUser": {
                        "admin": "xibiri"
                    }
                }"#.to_vec(),
                code_id: 0,
            }
        ),


        // D
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_D,
                message: br#"{
                    "AddUser": {
                        "admin": "lololo"
                    }
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_D,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_D,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_D,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_D,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_D,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),


        // I
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_I,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_I,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_I,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),


        // G
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_G,
                message: br#"{
                    "AddUser": {
                        "admin": "Balelas"
                    }
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_G,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_G,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_G,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),


        // C
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_C,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_C,
                message: br#"{
                    "AddOne": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_C,
                message: br#"{
                    "GetBalance": {}
                }"#.to_vec(),
                code_id: 0,
            }
        ),
    ]);

    let stop_time = start_time.elapsed();
    println!("Total execution time: {:?}", stop_time);

}


fn run_n_contracts_n_increments(n_contracts: u128, n_increments: u128) {
    let sc_manager: SCManager<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier> = SCManager::new();

    let mut mapping: HashMap<u128, HashMap<u128, ScAddr>> = HashMap::from([(0, HashMap::new())]);

    // create mapping (code_id, instantiation) -> address
    for i in 0..n_contracts {
        mapping.get_mut(&0).unwrap().insert(i, [i as u8; 32]);
    }


    let address_mapper = move |contract_code_id: u128, instantiation: u128| {
        mapping.get(&contract_code_id).unwrap().get(&instantiation).unwrap().clone()
    };

    let backend_builder = |storage| {
        mock_persistent_backend(&[], storage)
    };

    let concurrent_backend_builder = |tx_id: TxId, concurrent_schedule: Arc<ConcurrentSchedule>, 
        persistent_backend: Arc<PersistentBackend<MockApi, MockConcurrentStorage, MockQuerier>>, sc_address: &ScAddr, rws: Vec<ReadWrite>| {
        ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(tx_id, concurrent_schedule, persistent_backend, sc_address, rws)
    };

    let sc_manager = Arc::new(RwLock::new(sc_manager));


    let mut vm_manager = VMManager::new(
        Arc::clone(&sc_manager),
        Arc::new(address_mapper),
        Arc::new(backend_builder),
        Arc::new(concurrent_backend_builder),
    4,
    4);


    let mut msgs = vec![
        Message::Deployment { // deploy the contract before all
            contract_code:  CONTRACT,
        },  
    ];

    // instantiations
    for _ in 0..n_contracts {
        msgs.push(
            Message::Invocation(
                VMMessage::Instantiation {
                    contract_code_id: 0,
                    message: br#"{}"#.to_vec(),
                }
            )
        )
    }

    for i in 0..n_contracts {
        for _ in 0..n_increments {
            msgs.push(
                Message::Invocation(
                    VMMessage::Invocation {
                        entry_point: InstantiatedEntryPoint::Execute,
                        contract_address: [i as u8; 32],
                        message: br#"{
                            "AddOne": {}
                        }"#.to_vec(),
                        code_id: 0,
                    }
                )
            );
        }
    }

    // handle messages
    let mut message_handler = MessageHandler::new(
        sc_manager, 
        vm_manager,
        (3 * n_contracts * n_increments) as usize
    );
    
    let start = Instant::now();
    message_handler.handle_messages(msgs);
    let elapsed = start.elapsed();
    println!("Total Exec Time: {:?}", elapsed);

}

fn main() {
    // run_persistent_vm();
    run_n_contracts_n_increments(2, 500);
}
