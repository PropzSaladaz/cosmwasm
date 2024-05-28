// The external interface is `use cosmwasm_vm::testing::X` for all integration testing symbols, no matter where they live internally.

mod calls;
mod instance;
mod mock;
mod querier;
mod storage;

mod storage_partitioned;

pub use calls::{execute, instantiate, migrate, query, reply, sudo};
#[cfg(feature = "stargate")]
pub use calls::{
    ibc_channel_close, ibc_channel_connect, ibc_channel_open, ibc_packet_ack, ibc_packet_receive,
    ibc_packet_timeout,
};
pub use instance::{
    mock_instance, mock_instance_options, mock_instance_with_balances,
    mock_instance_with_failing_api, mock_instance_with_gas_limit, mock_instance_with_options,
    test_io, MockInstanceOptions,
};
pub use mock::{
    mock_backend, mock_persistent_backend, mock_concurrent_backend, mock_backend_with_balances, mock_env, mock_info, MockApi, MOCK_CONTRACT_ADDR,
};
pub use querier::MockQuerier;
pub use storage::MockStorage;

pub use storage_partitioned::{MockStoragePartitioned, MockStorageWrapper, StorageWrapper, ValueType, PartitionedStorage, BaseStorage};
