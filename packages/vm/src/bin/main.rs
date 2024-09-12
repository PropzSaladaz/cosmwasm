use std::{collections::HashMap, sync::{Arc, RwLock}, time::Instant};

use cosmwasm_vm::{
    testing::{mock_persistent_backend, MockApi, MockConcurrentStorage, MockQuerier, MockStorageWrapper}, AddressMapper, ConcurrentBackend, ConcurrentSchedule, InstantiatedEntryPoint, Message, MessageHandler, PersistentBackend, ReadWrite, SCManager, ScAddr, SymbolicExecutionEngine, TxId, VMManager, VMMessage};

const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");

fn run_n_contracts_n_increments(n_contracts: u128, n_operation_repetitions: u128) {
    let se_engine = SymbolicExecutionEngine::new();
    let sc_manager = SCManager::new(Arc::new(se_engine));

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


    // handle messages
    let mut message_handler = MessageHandler::new(
        sc_manager, 
        (10 * n_contracts * n_operation_repetitions) as usize,
        Arc::new(address_mapper),
        Arc::new(backend_builder),
        Arc::new(concurrent_backend_builder),
    4,
    4);


    let mut msgs = vec![
        Message::Deployment { // deploy the contract before all
            contract_code:  CONTRACT,
            code_id: None,
        },  
    ];

    // instantiations
    for _ in 0..n_contracts {
        msgs.push(
            Message::Invocation(
                VMMessage::Instantiation {
                    contract_code_id: 0,
                    message: br#"{}"#.to_vec(),
                    hash: "".to_owned(),
                    sender: "".to_owned(),
                    label: "".to_owned(),
                    funds: vec![],
                    reply: None,
                }
            )
        )
    }

    for i in 0..n_contracts {
        for _ in 0..n_operation_repetitions {
            msgs.push(
                Message::Invocation(
                    VMMessage::Invocation {
                        entry_point: InstantiatedEntryPoint::Execute,
                        contract_address: [i as u8; 32],
                        message: br#"{
                            "AddOne": {
                                "user": "ADMIN"
                            }
                        }"#.to_vec(),
                        hash: "".to_owned(),
                        sender: "".to_owned(),
                        funds: vec![],
                    }
                )
            );

            msgs.push(
                Message::Invocation(
                    VMMessage::Invocation {
                        entry_point: InstantiatedEntryPoint::Execute,
                        contract_address: [i as u8; 32],
                        message: br#"{
                            "SetVal": {
                                "user": "ADMIN",
                                "val": 10
                            }
                        }"#.to_vec(),
                        hash: "".to_owned(),
                        sender: "".to_owned(),
                        funds: vec![],
                    }
                )
            );
        }
    }

    
    let start = Instant::now();
    message_handler.handle_messages(msgs);
    let elapsed = start.elapsed();
    println!("Total Exec Time: {:?}", elapsed);

}

fn main() {
    // run_persistent_vm();
    run_n_contracts_n_increments(35, 30);
}
