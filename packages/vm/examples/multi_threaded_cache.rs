use std::sync::{Arc, RwLock};
use std::thread;
use tempfile::TempDir;

use cosmwasm_std::{coins, Empty};
use cosmwasm_vm::testing::{mock_backend, mock_env, mock_info, mock_persistent_backend, MockApi, MockQuerier, MockStorage, MockStoragePartitioned, MockStorageWrapper};
use cosmwasm_vm::{
    call_execute, call_instantiate, capabilities_from_csv, Cache, CacheOptions, ConcurrentBackend, InstanceOptions, Size
};

// Instance
const DEFAULT_MEMORY_LIMIT: Size = Size::mebi(64);
const DEFAULT_GAS_LIMIT: u64 = 400_000 * 150;
const DEFAULT_INSTANCE_OPTIONS: InstanceOptions = InstanceOptions {
    gas_limit: DEFAULT_GAS_LIMIT,
};
// Cache
const MEMORY_CACHE_SIZE: Size = Size::mebi(200);

static CONTRACT: &[u8] = include_bytes!("../testdata/hackatom.wasm");

const SAVE_WASM_THREADS: usize = 32;
const INSTANTIATION_THREADS: usize = 2048;
const THREADS: usize = SAVE_WASM_THREADS + INSTANTIATION_THREADS;

pub fn main() {
    let options = CacheOptions::new(
        TempDir::new().unwrap().into_path(),
        capabilities_from_csv("iterator,staking"),
        MEMORY_CACHE_SIZE,
        DEFAULT_MEMORY_LIMIT,
    );

    let cache: Cache<MockApi, MockStorageWrapper, MockQuerier> = unsafe { Cache::new(options).unwrap() };
    let cache = Arc::new(cache);

    let checksum = cache.save_wasm(CONTRACT).unwrap();

    let mut threads = Vec::with_capacity(THREADS);
    for _ in 0..SAVE_WASM_THREADS {
        let cache = Arc::clone(&cache);

        threads.push(thread::spawn(move || {
            let checksum = cache.save_wasm(CONTRACT).unwrap();
            println!("Done saving Wasm {checksum}");
        }));
    }
    for i in 0..INSTANTIATION_THREADS {
        let cache = Arc::clone(&cache);

        threads.push(thread::spawn(move || {
            let partitioned_storage = MockStoragePartitioned::default();
            let backend = Arc::new(mock_persistent_backend(&[], Arc::new(partitioned_storage)));
            let concurrent_backend = ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(backend, &String::from(""), vec![]);
            let mut instance = cache
                .get_instance(&checksum, concurrent_backend, DEFAULT_INSTANCE_OPTIONS)
                .unwrap();
            println!("Done instantiating contract {i}");

            let info = mock_info(&instance.api().addr_make("creator"), &coins(1000, "earth"));
            let verifier = instance.api().addr_make("verifies");
            let beneficiary = instance.api().addr_make("benefits");
            let msg = format!(r#"{{"verifier": "{verifier}", "beneficiary": "{beneficiary}"}}"#);
            let contract_result = call_instantiate::<_, _, _, Empty>(
                &mut instance,
                &mock_env(),
                &info,
                msg.as_bytes(),
            )
            .unwrap();
            assert!(contract_result.into_result().is_ok());

            let info = mock_info(&verifier, &coins(15, "earth"));
            let msg = br#"{"release":{}}"#;
            let contract_result =
                call_execute::<_, _, _, Empty>(&mut instance, &mock_env(), &info, msg).unwrap();
            assert!(contract_result.into_result().is_ok());
        }));
    }

    threads.into_iter().for_each(|thread| {
        thread
            .join()
            .expect("The threaded instantiation or execution failed !")
    });

    assert_eq!(cache.stats().misses, 0);
    assert_eq!(cache.stats().hits_pinned_memory_cache, 0);
    assert_eq!(
        cache.stats().hits_memory_cache,
        INSTANTIATION_THREADS as u32 - 1
    );
    assert_eq!(cache.stats().hits_fs_cache, 1);
}
