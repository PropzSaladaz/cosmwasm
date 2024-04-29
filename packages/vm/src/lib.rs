mod backend;
mod cache;
mod calls;
mod capabilities;
mod compatibility;
mod conversion;
mod environment;
mod errors;
mod filesystem;
mod imports;
mod instance;
mod limited;
mod memory;
mod modules;
mod parsed_wasm;
mod sections;
mod serde;
mod size;
mod static_analysis;
pub mod testing;
mod wasm_backend;

mod symb_exec;
mod msg_handler;
mod vm_manager;

pub use crate::backend::{
    Backend, BackendApi, BackendError, BackendResult, GasInfo, Querier, Storage,
};
pub use crate::cache::{AnalysisReport, Cache, CacheOptions, Metrics, Stats};
pub use crate::calls::{
    call_execute, call_execute_raw, call_instantiate, call_instantiate_raw, call_migrate,
    call_migrate_raw, call_query, call_query_raw, call_reply, call_reply_raw, call_sudo,
    call_sudo_raw,
};
#[cfg(feature = "stargate")]
pub use crate::calls::{
    call_ibc_channel_close, call_ibc_channel_close_raw, call_ibc_channel_connect,
    call_ibc_channel_connect_raw, call_ibc_channel_open, call_ibc_channel_open_raw,
    call_ibc_packet_ack, call_ibc_packet_ack_raw, call_ibc_packet_receive,
    call_ibc_packet_receive_raw, call_ibc_packet_timeout, call_ibc_packet_timeout_raw,
};
pub use crate::capabilities::capabilities_from_csv;
pub use crate::errors::{
    CommunicationError, CommunicationResult, RegionValidationError, RegionValidationResult,
    VmError, VmResult,
};
pub use crate::instance::{DebugInfo, GasReport, Instance, InstanceOptions};
pub use crate::serde::{from_slice, to_vec};
pub use crate::size::Size;

pub use crate::symb_exec::{SCProfile, SCProfileParser, SEStatus};
pub use crate::msg_handler::{MessageHandler, Message};
pub use crate::vm_manager::{SCManager, VMMessage, VMManager, InstantiatedEntryPoint, DepsMut};

#[doc(hidden)]
pub mod internals {
    //! We use the internals module for exporting types that are only
    //! intended to be used in internal crates / utils.
    //! Please don't use any of these types directly, as
    //! they might change frequently or be removed in the future.

    pub use crate::compatibility::check_wasm;
    pub use crate::instance::instance_from_module;
    pub use crate::wasm_backend::{compile, make_compiling_engine, make_runtime_engine};
}

