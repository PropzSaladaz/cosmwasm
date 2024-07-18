use std::{collections::HashMap, sync::{Arc, RwLock}, time::Instant};

use cosmwasm_vm::{
    testing::{mock_persistent_backend, MockApi, MockConcurrentStorage, MockQuerier}, InstantiatedEntryPoint, Message, MessageHandler, SCManager, ScAddr, VMManager, VMMessage};

const SC_ADDR_A: ScAddr = *b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const SC_ADDR_B: ScAddr = *b"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const SC_ADDR_C: ScAddr = *b"cccccccccccccccccccccccccccccccc";
const SC_ADDR_D: ScAddr = *b"dddddddddddddddddddddddddddddddd";
const SC_ADDR_E: ScAddr = *b"eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
const SC_ADDR_F: ScAddr = *b"ffffffffffffffffffffffffffffffff";
const SC_ADDR_G: ScAddr = *b"gggggggggggggggggggggggggggggggg";
const SC_ADDR_H: ScAddr = *b"hhhhhhhhhhhhhhhhhhhhhhhhhhhhhhhh";
const SC_ADDR_I: ScAddr = *b"iiiiiiiiiiiiiiiiiiiiiiiiiiiiiiii";


fn run_persistent_vm() {

    // Read test smart contract code
    let code = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");

    let sc_manager: SCManager<MockApi, MockConcurrentStorage, MockQuerier> = SCManager::new();

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

    let sc_manager = Arc::new(RwLock::new(sc_manager));

    let vm_manager = VMManager::new(
        Arc::clone(&sc_manager),
        Arc::new(address_mapper),
        Arc::new(backend_builder),
    1);
    // handle messages
    let mut message_handler = MessageHandler::new(
        sc_manager, 
        vm_manager,
        50
    );
    
    let start_time = Instant::now();

    message_handler.handle_messages(vec![
        Message::Deployment { 
            contract_code:  code,
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

fn main() {
    run_persistent_vm();
}
