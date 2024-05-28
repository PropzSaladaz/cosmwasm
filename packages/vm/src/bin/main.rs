use std::{collections::HashMap, sync::{Arc, RwLock}};

use cosmwasm_vm::{
    testing::{mock_persistent_backend, MockApi, MockQuerier, MockStoragePartitioned}, 
    InstantiatedEntryPoint, Message, MessageHandler, SCManager, VMManager, VMMessage};

fn run_persistent_vm() {

    // Read test smart contract code
    let code = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");

    let sc_manager: SCManager<MockApi, MockStoragePartitioned, MockQuerier> = SCManager::new();

    // create mapping (code_id, instantiation) -> address
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

    let backend_builder = |storage| {
        mock_persistent_backend(&[], storage)
    };

    let sc_manager = Arc::new(RwLock::new(sc_manager));

    let vm_manager = VMManager::new(
        Arc::clone(&sc_manager),
        Box::new(address_mapper),
        2,
        Box::new(backend_builder));
    // handle messages
    let mut message_handler = MessageHandler::new(
        sc_manager, 
        vm_manager
    );
    
    message_handler.handle_messages(vec![
        Message::Deployment { 
            contract_code:  code,
        },
        Message::Invocation(
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#,
                sender_address: String::from(""),
            }
        ),
        Message::Invocation(
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: "a".to_owned(),
                code_id: 0,
                message: br#"{
                    "AddOne": {}
                }"#,
                sender_address: String::from("")
            }
        ),
    ]);

}

fn main() {
    run_persistent_vm();
}
