use cosmwasm_std::{coins, to_json_string, Empty};
use cosmwasm_vm::testing::{mock_backend, mock_env, mock_info, MockApi};
use cosmwasm_vm::{call_execute, call_instantiate, call_query, BackendApi, Instance, InstanceOptions, Querier, SCProfile, SCProfileParser, Size, Storage};
use simple_logging;
use log::LevelFilter;
use cosmwasm_vm::internals::{compile, make_compiling_engine, instance_from_module};
use wasmer::Store;


//use wasm_backend::{compile, make_store_with_engine};

// Instance
const DEFAULT_MEMORY_LIMIT: Size = Size::mebi(64);
const DEFAULT_GAS_LIMIT: u64 = 1_000_000_000_000; // ~1ms
const DEFAULT_INSTANCE_OPTIONS: InstanceOptions = InstanceOptions {
        gas_limit: DEFAULT_GAS_LIMIT,
        // print_debug: false,
    };
const HIGH_GAS_LIMIT: u64 = 20_000_000_000_000_000; // ~20s, allows many calls on one instance
static CONTRACT: &[u8] = include_bytes!("../../custom_contracts/test-contract/target/wasm32-unknown-unknown/release/contract.wasm");
static CONTRACT_INSTANTIATE: &[u8] = br#"{
    }"#;

static CONTRACT_QUERY: &[u8] = br#"{
        "GetBalance": {
            "acc_name": "New_user"
        }
    }"#;

static CONTRACT_EXECUTE: &[u8] = br#"{
    "SimpleAddUser": {
        "user": "New_user"
    }
}"#;

static EXECUTE_OWNED_ACC: &[u8] = br#"{
    "ComplexExecute": {
        "CreateAcc": {
            "acc_name": "acc1"
        }
    }
}"#;

static EXECUTE_SHARED_ACC: &[u8] = br#"{
    "ComplexExecute": {
        "CreateSharedAcc": {
            "acc_name": "acc2",
            "owners": ["o1", "o2"]
        }
    }
}"#;

static EXECUTE_DEPOSIT: &[u8] = br#"{
    "ComplexExecute": {
        "Deposit": {
            "acc_name": "acc1",
            "owner": "",
            "amount": "250"
        }
    }
}"#;

static EXECUTE_TRANSFER: &[u8] = br#"{
    "ComplexExecute": {
        "Transfer": {
            "acc_from": "acc1",
            "acc_to": "acc2",
            "shared_owner": "",
            "amount": "20"
        }
    }
}"#;

static QUERY_ACC_DETAILS1: &[u8] = br#"{
    "GetAccDetails": {
        "acc_name": "acc1"
    }
}"#;

static QUERY_ACC_DETAILS2: &[u8] = br#"{
    "GetAccDetails": {
        "acc_name": "acc2"
    }
}"#;

static QUERY_BANK_ANALYTICS: &[u8] = br#"{
    "GetBankAnalytics": {}
}"#;

fn run_threads(nb_instantiations: u32, nb_threads: u32, pre_compile: bool) {

    let start = std::time::Instant::now();
    let mut threads = vec![];
    for _ in 0 ..nb_threads {

        println!("Thread started!");

        threads.push( std::thread::spawn(move || {

            let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
            let module = compile( &engine, CONTRACT).unwrap();
            for _ in 0.. (nb_instantiations/nb_threads) {

                println!("Running a task!");

                let backend = mock_backend(&[]);
                let much_gas: InstanceOptions = InstanceOptions {
                    gas_limit: HIGH_GAS_LIMIT,
                    ..DEFAULT_INSTANCE_OPTIONS
                };


                let mut instance = {
                    if pre_compile {
                      let store = Store::new(engine.clone());
                        instance_from_module(store, &module, backend, much_gas.gas_limit, None).unwrap()
                    } else {
                        Instance::from_code( CONTRACT, backend, much_gas, Some(DEFAULT_MEMORY_LIMIT)).unwrap()
                    }
                };

                let contract_result =
                call_instantiate::<_, _, _, Empty>(&mut instance, &mock_env(), &mock_info("lalaland", &[]), CONTRACT_INSTANTIATE).unwrap();
                println!("CONTRACT_INSTANTIATE RESULT: {:#?}", contract_result);

                // simple state executions
                let contract_result =
                call_execute::<_, _, _, Empty>(&mut instance, &mock_env(), &mock_info("lalaland", &[]), CONTRACT_EXECUTE);
                println!("execute RESULT: {:#?}", contract_result);

                let contract_result =
                call_query::<_, _, _>(&mut instance, &mock_env(), CONTRACT_QUERY);
                println!("query RESULT: {:#?}", String::from_utf8(base64::decode(contract_result.unwrap().unwrap().to_string()).unwrap()).unwrap());


                // complex state executions
                let contract_result =
                call_execute::<_, _, _, Empty>(&mut instance, &mock_env(), &mock_info("lalaland", &[]), EXECUTE_OWNED_ACC);
                println!("EXECUTE_OWNED_ACC RESULT: {:#?}", contract_result);

                let contract_result =
                call_execute::<_, _, _, Empty>(&mut instance, &mock_env(), &mock_info("lalaland", &[]), EXECUTE_SHARED_ACC);
                println!("EXECUTE_SHARED_ACC RESULT: {:#?}", contract_result);

                let contract_result =
                call_execute::<_, _, _, Empty>(&mut instance, &mock_env(), &mock_info("lalaland", &[]), EXECUTE_DEPOSIT);
                println!("EXECUTE_DEPOSIT RESULT: {:#?}", contract_result);

                let contract_result =
                call_execute::<_, _, _, Empty>(&mut instance, &mock_env(), &mock_info("lalaland", &[]), EXECUTE_TRANSFER);
                println!("EXECUTE_TRANSFER RESULT: {:#?}", contract_result);

                let contract_result =
                call_query::<_, _, _>(&mut instance, &mock_env(), QUERY_ACC_DETAILS1);
                println!("QUERY_ACC_DETAILS1 RESULT: {:#?}", String::from_utf8(base64::decode(contract_result.unwrap().unwrap().to_string()).unwrap()).unwrap());

                let contract_result =
                call_query::<_, _, _>(&mut instance, &mock_env(), QUERY_ACC_DETAILS2);
                println!("QUERY_ACC_DETAILS2 RESULT: {:#?}", String::from_utf8(base64::decode(contract_result.unwrap().unwrap().to_string()).unwrap()).unwrap());

                let contract_result =
                call_query::<_, _, _>(&mut instance, &mock_env(), QUERY_BANK_ANALYTICS);
                println!("QUERY_BANK_ANALYTICS RESULT: {:#?}", String::from_utf8(base64::decode(contract_result.unwrap().unwrap().to_string()).unwrap()).unwrap());

            }
        }));
    }

    for h in threads {
        h.join().unwrap();
    }
    let stop = std::time::Instant::now();
    println!("Elapsed precompile: {} threads {} : time: {:?}", pre_compile, nb_threads, stop.duration_since(start));
}


fn main() {

    simple_logging::log_to_stderr(LevelFilter::Trace);
    let nb_instantiations = 1;
    run_threads(nb_instantiations, 1, false);

    // let current_dir = std::env::current_dir().unwrap();
    // let profile = SCProfileParser::from_file(
    //     current_dir.join("custom_contracts").join("empty-contract").join("se-out.txt").to_str().unwrap());
    // println!("Profile: {:?}", profile);

}
