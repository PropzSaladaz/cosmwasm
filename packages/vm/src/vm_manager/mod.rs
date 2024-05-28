mod sc_storage;
mod vm_manager;

pub use vm_manager::{VMManager, VMMessage, AddressMapper, InstantiatedEntryPoint, DepsMut};
pub use sc_storage::{SCManager, ContractRWS, PersistentBackend};