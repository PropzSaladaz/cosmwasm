use std::{collections::HashMap, rc::Rc, sync::{Arc, RwLock}, time::Instant};

use cosmwasm_vm::{
    testing::{mock_persistent_backend, MockApi, MockConcurrentStorage, MockQuerier, MockStorageWrapper}, vm_transactions::{ExecuteTx, InstantiateTx, SerializableTransaction, TransactionEnum}, ConcurrentBackend, ConcurrentSchedule, InstantiatedEntryPoint, Message, MessageHandler, PersistentBackend, ReadWrite, SCManager, ScAddr, SymbolicExecutionEngine, TxId
};

const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");

fn run_n_contracts_n_increments(n_contracts: u128, n_operation_repetitions: u128) {
    let se_engine = SymbolicExecutionEngine::new();
    let sc_manager = SCManager::new(Arc::new(se_engine));

    let backend_builder = |storage| {
        mock_persistent_backend(&[], storage)
    };

    let concurrent_backend_builder = |tx_id: TxId, concurrent_schedule: Rc<Arc<ConcurrentSchedule>>, 
        persistent_backend: Arc<PersistentBackend<MockApi, MockConcurrentStorage, MockQuerier>>, sc_address: ScAddr, rws: Vec<ReadWrite>| {
        ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(tx_id, concurrent_schedule, persistent_backend, sc_address, rws)
    };

    let sc_manager = Arc::new(RwLock::new(sc_manager));


    // handle messages
    let mut message_handler = MessageHandler::new(
        sc_manager, 
        (10 * n_contracts * n_operation_repetitions) as usize,
        Arc::new(backend_builder),
        Arc::new(concurrent_backend_builder),
    2,
    2);


    let mut msgs = vec![
        Message::Deployment { // deploy the contract before all
            contract_code:  CONTRACT,
            code_id: None,
        },  
    ];

    // instantiations
    for i in 0..n_contracts {
        msgs.push(
            Message::Invocation(
                SerializableTransaction::with_log_instantiate(
                    TransactionEnum::Instantiate(InstantiateTx {
                        code_id: 0,
                        msg: br#"{}"#.to_vec(),
                        hash: "".to_owned(),
                        sender: "".to_owned(),
                        label: "".to_owned(),
                        funds: vec![],
                        reply: None,
                    }),
                    HashMap::from([(0u32, vec![format!("{:?}", i)])])
                )
            )
        )
    }

    for i in 0..n_contracts {
        for _ in 0..n_operation_repetitions {
            msgs.push(
                Message::Invocation(
                    SerializableTransaction::with_log_execute(
                        TransactionEnum::Execute(ExecuteTx {
                            msg: br#"{
                                "AddOne": {
                                    "user": "ADMIN"
                                }
                            }"#.to_vec(),
                            contract_addr: format!("{:?}", i),
                            hash: "".to_owned(),
                            sender: "".to_owned(),
                            funds: vec![],
                            reply: None,
                        }),
                        vec![format!("{:?}", i)]
                    )
                )
            );

            msgs.push(
                Message::Invocation(
                    SerializableTransaction::with_log_execute(
                        TransactionEnum::Execute(ExecuteTx {
                            msg: br#"{
                                "SetVal": {
                                    "user": "ADMIN",
                                    "val": 10
                                }
                            }"#.to_vec(),
                            contract_addr: format!("{:?}", i),
                            hash: "".to_owned(),
                            sender: "".to_owned(),
                            funds: vec![],
                            reply: None,
                        }),
                        vec![format!("{:?}", i)]
                    )
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
    run_n_contracts_n_increments(2, 2);
}
