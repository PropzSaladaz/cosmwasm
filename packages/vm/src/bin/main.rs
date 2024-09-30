use std::{collections::HashMap, fs::File, io::BufReader, rc::Rc, sync::{Arc, RwLock}, time::Instant};

use cosmwasm_vm::{
    testing::{mock_persistent_backend, perfect_rws_engine::PerfectRWSEngine, MockApi, MockConcurrentStorage, MockQuerier, MockStorageWrapper}, vm_transactions::{ExecuteTx, InstantiateTx, SerializableTransaction, StoreCodeTx, TransactionEnum}, ConcurrentBackend, ConcurrentSchedule, ContractRWS, InstantiatedEntryPoint, Message, MessageHandler, PersistentBackend, ReadWrite, SCManager, SCStorage, ScAddr, SymbolicExecutionEngine, TxId
};

const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");

fn run_n_contracts_n_increments(n_contracts: u128, n_operation_repetitions: u128) {
    let se_engine = PerfectRWSEngine::new();
    let sc_manager = SCManager::new(Arc::new(se_engine));

    let backend_builder = |storage| {
        mock_persistent_backend(&[], storage)
    };

    let concurrent_backend_builder = |tx_id: TxId, concurrent_schedule: Rc<Arc<ConcurrentSchedule>>, 
        persistent_backend: Arc<PersistentBackend<MockApi, MockConcurrentStorage, MockQuerier>>, sc_storages: Arc<SCStorage<MockApi, MockConcurrentStorage, MockQuerier>>, rws: Vec<ContractRWS>, starting_sc_address: ScAddr| {
        ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(tx_id, concurrent_schedule, persistent_backend, sc_storages, rws, starting_sc_address)
    };

    let sc_manager = Arc::new(RwLock::new(sc_manager));


    // handle messages
    let mut message_handler = MessageHandler::new(
        sc_manager, 
        (10 * n_contracts * n_operation_repetitions) as usize,
        Arc::new(backend_builder),
        Arc::new(concurrent_backend_builder),
    6,
    6);

        // reads txs from file
    let file = File::open("/home/sidnei-teixeira/Documents/ResumosLEIC/MEIC-1ano/Tese/cosmwasm_original/cosmwasm/packages/vm").unwrap();
    let reader = BufReader::new(file);
    let txs: Vec<SerializableTransaction> = serde_json::from_reader(reader).unwrap();
    // convert txs to MessageHandler wrapper
    let txs = txs.into_iter().map(|tx| match tx.transaction {
        TransactionEnum::StoreCode(StoreCodeTx { wasm, log_store_code, ..}) => 
            Message::Deployment { contract_code: wasm, code_id: Some(log_store_code as u32) },
        _ => Message::Invocation(tx)
    }).collect();


    let start = Instant::now();
    message_handler.handle_messages(txs);
    let elapsed = start.elapsed();
    println!("Total Exec Time: {:?}", elapsed);

}

fn main() {
    // run_persistent_vm();
    run_n_contracts_n_increments(30, 35);
}
