use std::{collections::HashMap, sync::{Arc, RwLock}, thread};

use indexmap::IndexMap;
use parking_lot::Mutex;

use cosmwasm_std::{Addr, Api, Binary, Coin, CustomQuery, Empty, IbcAcknowledgement, IbcOrder, IbcTimeout, QuerierWrapper, Reply};
use rkyv::Archive;
use serde::{Deserialize, Serialize};
use wasmer::Store;

use crate::{
    backend::ConcurrentBackend, call_execute, call_instantiate, call_query, internals::instance_from_module, 
    symb_exec::{ProfileEvaluator, ProfileGenerator, ReadWrite, SEStatus, StorageDependency, TxRWS}, 
    testing::{mock_env, mock_info, ConcurrentStorage, StorageWrapper}, 
    wasm_backend::{compile, make_compiling_engine}, 
    BackendApi, ConcurrentSchedule, InstanceOptions, Querier, SCProfile, Size,
};

use super::{sc_storage::{PersistentBackend, SCManager}, schedule::{ScAddr, TxId}, ParallelScheduleBuilder};

const DEFAULT_MEMORY_LIMIT: Size = Size::mebi(64);
const HIGH_GAS_LIMIT: u64 = 20_000_000_000_000_000; // ~20s, allows many calls on one instance

#[cfg(feature = "exec_time")]
use std::time::{Duration, Instant};

#[derive(PartialEq)]
enum BatchType {
    Instantiation,
    Invocation
}

enum VMCall {
    Execute,
    Query,
}

#[derive(Debug, Serialize, Deserialize, PartialEq, Clone)]
pub struct ReplyStruct {
    reply_on: bool,
    reply_id: u64,
    reply_payload: Binary,
    reply_address: String,
}

#[derive(Debug, PartialEq, Clone)]
pub enum VMMessage {
    Instantiation {
        hash: String,
        sender: String,
        label: String,
        funds: Vec<Coin>,
        message: Vec<u8>,
        contract_code_id: u128,

        reply: Option<ReplyStruct>, // replay txs
    },
    Invocation {
        hash: String,
        sender: String,
        funds: Vec<Coin>,

        entry_point: InstantiatedEntryPoint,
        message: Vec<u8>,
        contract_address: ScAddr,
    },
    Reply {
        message: Reply,
        contract_address: String,
    },
    ChannelOpenInitTx {
        hash: String,
        ordering: IbcOrder,
        port_id: String,
        channel_id: String,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        connection_id: String,
        version: String,
    },
    ChannelOpenTryTx {
        hash: String,
        ordering: IbcOrder,
        port_id: String,
        channel_id: String,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        connection_id: String,
        version: String,
    },
    ChannelOpenAckTx {
        hash: String,
        port_id: String,
        channel_id: String,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        connection_id: String,
    },
    ChannelOpenConfirmTx {
        hash: String,
        port_id: String,
        channel_id: String,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        connection_id: String,
    },
    RecvPacketTx {
        hash: String,
        relayer: Addr,
        data: Binary,
        port_id: String,
        channel_id: String,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        sequence: u64,
        timeout: IbcTimeout
    },
    TimeoutTx {
        hash: String,
        relayer: Addr,
        data: Binary,
        port_id: String,
        channel_id: String,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        sequence: u64,
        timeout: IbcTimeout
    },
    AckTx {
        hash: String,
        acknowledgement: IbcAcknowledgement,
        relayer: Addr,
        data: Binary,
        port_id: String,
        channel_id: String,
        counterparty_port_id: String,
        counterparty_channel_id: String,
        sequence: u64,
        timeout: IbcTimeout
    },
    NotSupportedTx {
        hash: String,
        tx_type: String,
    },
    AbortTx {
        hash: String,
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum InstantiatedEntryPoint {
    Execute,
    Query,
    Migrate,
}


pub type Block = Vec<VMMessage>;

/// These are functions that must be defined by whoever constructs the VMManager,
/// such that it returns the expected generic tpyes. THis is used so that we only work with generic types
/// mapping (code_id, nth_instantiation) => address
pub type AddressMapper = dyn Fn(u128, u128) -> ScAddr + Sync + Send;
pub type BackendBuilder<A, S, Q> = dyn Fn(Arc<S>) -> PersistentBackend<A, S, Q> + Send + Sync;
pub type ConcurrentBackendBuilder<A, S, W, Q> = dyn Fn(
    TxId,  // tx_block_id
    Arc<ConcurrentSchedule>, 
    Arc<PersistentBackend<A, S, Q>>,
    &ScAddr,
    Vec<ReadWrite>) -> ConcurrentBackend<A, W, Q> + Send + Sync;

struct ThreadExecutionContext<A, S, W, Q, E>
where
    A: BackendApi + 'static + Sync + Send,
    S: ConcurrentStorage + 'static + Sync + Send,
    W: StorageWrapper + 'static,
    Q: Querier + 'static + Sync + Send, 
    E: ProfileGenerator
{
    state_manager:  Arc<RwLock<SCManager<A, S, W, Q, E>>>,
    backend_builder: Arc<BackendBuilder<A, S, Q>>,
    concurrent_backend_builder: Arc<ConcurrentBackendBuilder<A, S, W, Q>>,
    max_concurrent_vms: u16,
}


/// This is a read-only version of depsMut -> we won't change anything
/// in it when parsing the RWS, thus storage can be a immutable reference
pub struct DepsMut<'a, C: CustomQuery = Empty> {
    pub storage: &'a dyn cosmwasm_std::Storage,
    pub api: &'a dyn Api,
    pub querier: QuerierWrapper<'a, C>,
}

type TransactionBatch = Vec<VMMessage>;

/// Used to keep a connection between a RWS and a message that originated that RWS.
/// This is first used when fetching the list of RWS given a block of messages, and then is
/// passed to the execution.
#[derive(Debug, Clone)]
pub struct RWSContext {
    pub rws: TxRWS,
    pub address: ScAddr, 
    pub tx_message: Option<VMMessage>,
    pub tx_block_id: TxId,

}

impl PartialEq for RWSContext {
    fn eq(&self, other: &Self) -> bool {
        self.rws == other.rws && 
        self.address == other.address &&
        match (&self.tx_message, &other.tx_message) {
            (Some(a), Some(b)) => a == b,
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        }
    }
}

/// Stateful manager used to instantiate VMs for contract execution,
/// passing them a reference to its corresponding persistent storage
pub struct VMManager<A, S, W, Q, E>
where
    A: BackendApi                           + 'static + Send + Sync,
    S: ConcurrentStorage                    + 'static + Send + Sync,
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Send + Sync,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Send + Sync,
{
    
    /// Stores SCs and their profiles
    state_manager: Arc<RwLock<SCManager<A, S, W, Q, E>>>,

    symb_exec_engine: Arc<E>,

    /// will be computed when blockchain is replayed, & when we instantiate contracts, etc we
    /// will use the addresses from the replay
    address_mapper: Arc<AddressMapper>,
    
    backend_builder: Arc<BackendBuilder<A, S, Q>>, 
    concurrent_backend_builder: Arc<ConcurrentBackendBuilder<A, S, W, Q>>,

    n_threads: u16,

    /// States the max number of instantiated VMs for a given SC.
    /// Multiple vms for the same SC are useful when multiple txs for the 
    /// same CS can be parallelized - in cases where we have commutative operations. 
    /// This is a workaround since we cannot use the same VM to execute 
    /// different txs concurrently.
    /// Also, this number is fixed throughout the entire execution, as we instantiate
    /// all VMs upon the 1st instantiation message for the corresponding contract
    max_concurrent_instances: u16,

    #[cfg(feature = "debug_graph")]
    block_number: u128,

    #[cfg(feature = "exec_time")]
    schedule_build_timer: Option<Instant>,
    #[cfg(feature = "exec_time")]
    schedule_build_time: Duration,
    #[cfg(feature = "exec_time")]
    instantiation_calls_timer: Option<Instant>,
    #[cfg(feature = "exec_time")]
    instantiation_calls_time: Duration,
    #[cfg(feature = "exec_time")]
    schedule_execution_timer: Option<Instant>,
    #[cfg(feature = "exec_time")]
    schedule_execution_time: Duration,
    #[cfg(feature = "exec_time")]
    schedule_persistence_timer: Option<Instant>,
    #[cfg(feature = "exec_time")]
    schedule_persistence_time: Duration,
}

impl<A, S, W, Q, E> VMManager<A, S, W, Q, E> 
where
    A: BackendApi                           + Sync + Send, 
    S: ConcurrentStorage                    + Sync + Send, 
    W: StorageWrapper,
    Q: Querier                              + Sync + Send,
    E: ProfileEvaluator + ProfileGenerator  + 'static + Sync + Send,
{

    pub fn new(
        state_manager: Arc<RwLock<SCManager<A, S, W, Q, E>>>, 
        address_mapper: Arc<AddressMapper>,
        backend_builder: Arc<BackendBuilder<A, S, Q>>,
        concurrent_backend_builder: Arc<ConcurrentBackendBuilder<A, S, W, Q>>, 
        n_threads: u16, max_concurrent_instances: u16) -> Self
    {
        // get symb. exec. engine from state manager
        let se_engine = Arc::clone(&state_manager.read().unwrap().get_symb_exec_engine());

        VMManager {
            state_manager,
            symb_exec_engine: se_engine,
            address_mapper,
            backend_builder,
            n_threads,
            max_concurrent_instances,
            concurrent_backend_builder,

            #[cfg(feature = "debug_graph")]
            block_number: 0,

            #[cfg(feature = "exec_time")]
            schedule_build_timer: None,
            #[cfg(feature = "exec_time")]
            schedule_build_time: Duration::ZERO,
            #[cfg(feature = "exec_time")]
            instantiation_calls_timer: None,
            #[cfg(feature = "exec_time")]
            instantiation_calls_time: Duration::ZERO,
            #[cfg(feature = "exec_time")]
            schedule_execution_timer: None,
            #[cfg(feature = "exec_time")]
            schedule_execution_time: Duration::ZERO,
            #[cfg(feature = "exec_time")]
            schedule_persistence_timer: None,
            #[cfg(feature = "exec_time")]
            schedule_persistence_time: Duration::ZERO,
        }
    }

    #[cfg(feature = "exec_time")]
    fn reset_timers(&mut self) {
        use std::time::Duration;

        self.schedule_build_timer = None;
        self.schedule_build_time = Duration::ZERO;
        self.instantiation_calls_timer = None;
        self.instantiation_calls_time = Duration::ZERO;
        self.schedule_execution_timer = None;
        self.schedule_execution_time = Duration::ZERO;
        self.schedule_persistence_timer = None;
        self.schedule_persistence_time = Duration::ZERO;
    }

    #[cfg(feature = "debug_graph")]
    fn increase_current_block_counter(&mut self) {
        self.block_number += 1;
    }

    // --- Schedule build timer ---
    #[cfg(feature = "exec_time")]
    fn start_schedule_build_timer(&mut self) {
        self.schedule_build_timer = Some(Instant::now());
    }

    #[cfg(feature = "exec_time")]
    fn stop_schedule_build_timer(&mut self) {
        let elapsed = self.schedule_build_timer.unwrap().elapsed();
        self.schedule_build_time += elapsed;
    }

    // --- VM instantiation timer ---
    #[cfg(feature = "exec_time")]
    fn start_instantiation_calls_timer(&mut self) {
        self.instantiation_calls_timer = Some(Instant::now());
    }

    #[cfg(feature = "exec_time")]
    fn stop_instantiation_calls_timer(&mut self) {
        let elapsed = self.instantiation_calls_timer.unwrap().elapsed();
        self.instantiation_calls_time += elapsed;
    }

    // --- Schedule execution timer ---
    #[cfg(feature = "exec_time")]
    fn start_schedule_execution_timer(&mut self) {
        self.schedule_execution_timer = Some(Instant::now());
    }

    #[cfg(feature = "exec_time")]
    fn stop_schedule_execution_timer(&mut self) {
        let elapsed = self.schedule_execution_timer.unwrap().elapsed();
        self.schedule_execution_time += elapsed;
    }

    // --- Schedule persistence timer ---
    #[cfg(feature = "exec_time")]
    fn start_schedule_persistence_timer(&mut self) {
        self.schedule_persistence_timer = Some(Instant::now());
    }

    #[cfg(feature = "exec_time")]
    fn stop_schedule_persistence_timer(&mut self) {
        let elapsed = self.schedule_persistence_timer.unwrap().elapsed();
        self.schedule_persistence_time += elapsed;
    }

    fn separate_instantiations_from_invocation(&self, block: Block) -> Vec<TransactionBatch> {
        let mut instantiations = Vec::with_capacity(block.len());
        let mut invocations = Vec::with_capacity(block.len());

        for tx in block {
            match tx {
                VMMessage::Instantiation { .. } => instantiations.push(tx),
                _ => invocations.push(tx),
            }
        };

        vec![instantiations, invocations]
    }

    /// Given a block of messages, fetch the RWS for each individual tx - this is done using information from the
    /// contract inputs and the already built SE profile when the SC was installed.
    /// 
    /// Then build a schedule from the RWS, marking all the dependencies across operations.
    /// Execute in arallel respecting the dependencies across operations.
    /// 
    /// At the end of execution, persist the final state to storage.
    pub fn handle_block(&mut self, block: Block) -> std::io::Result<Vec<String>> {
        #[cfg(feature = "exec_time")]
        self.reset_timers();

        let txs_batch = self.separate_instantiations_from_invocation(block);
        let mut resps = vec![];
        
        // There will ever only be 2 sets of txs.
        // 1 for the instantiations, which is the first to get executed.
        // a 2nd for all the other txs in the block.
        for (idx, batch) in txs_batch.into_iter().enumerate() {

            #[cfg(feature = "tx_reordering")]
            let mut rws: Vec<RWSContext> = self.get_ordered_rws(batch);
            #[cfg(not(feature = "tx_reordering"))]
            let mut rws: Vec<RWSContext> = self.get_original_ordered_rws(batch); 
            
            #[cfg(feature = "exec_time")]
            self.start_schedule_build_timer();
    
            let schedule = ParallelScheduleBuilder::build_from_rws(&mut rws, self.n_threads);
    
            #[cfg(feature = "exec_time")]
            self.stop_schedule_build_timer();

            let batch = if idx == 0 { BatchType::Instantiation } else { BatchType::Invocation };
            let mut resp = self.execute_block(rws, schedule, batch).unwrap();
            resps.append(&mut resp);
        }

        #[cfg(feature = "exec_time")]
        {
            println!("\n\nExecution Time ------");
            println!("Instantiation Calls  Execution: {:?}",      self.instantiation_calls_time);
            println!("---");
            println!("Invocation Calls Total Exec Time: {:?}", self.schedule_build_time + self.schedule_execution_time + self.schedule_persistence_time);
            println!("Invocation Calls Schedule Creation: {:?}",                   self.schedule_build_time);
            println!("Invocation Calls Schedule Execution: {:?}",          self.schedule_execution_time);
            println!("Invocation Calls Schedule Persistence: {:?}\n------\n\n",    self.schedule_persistence_time);
        }

        #[cfg(feature = "debug_graph")]
        self.increase_current_block_counter();


        Ok(resps)
    }


    /// Get the RWS given an input message for some contract.
    /// Fetches the SE profile, parses it & gets the final RWS in form of keys as bytes
    /// It returns a vec where each item contains the contract address as well as all the keys
    /// it will touch
    /// The return vector places all Instantiations first, then all COMPLETE & INDEPENDENT txs, and only after all the INCOMPLETE or DEPENDENT txs
    /// 
    /// Within all the instantiations/invocations there is still an order applied:
    /// - The 1st tx with some rws_uid sets the order for all the remaining txs with the same rws_uid in the current block
    /// - Txs with the same rws_uid are appended according to their position in the original block 
    #[allow(dead_code)]
    fn get_ordered_rws(&self, block: Block) -> Vec<RWSContext> {
        let mut final_tx_order = vec![];

        // will store txs that have the same RWS as key (RWS_ID) -> value (vec of txs, ordered by order of appearence)
        let mut rws_complete_and_independent_tx_map = IndexMap::new();
        let mut rws_incomplete_or_dependent_tx_map = IndexMap::new();

        self.save_rws(
            block, 
            |tx| {
                if (tx.rws.profile_status == SEStatus::Complete) && (tx.rws.storage_dependency == StorageDependency::Independent) {
                    let same_profile_txs = rws_complete_and_independent_tx_map.entry(tx.rws.rws_uid.clone()).or_insert(vec![]);
                    same_profile_txs.push(tx);
                }
                else {
                    let same_profile_txs = rws_incomplete_or_dependent_tx_map.entry(tx.rws.rws_uid.clone()).or_insert(vec![]);
                    same_profile_txs.push(tx);
                }
            }
        );


        // append complete and independent first
        for (_key, mut value) in rws_complete_and_independent_tx_map {
            final_tx_order.append(&mut value);
        }

        // append incomplete || dependent RWSs at the end
        for (_key, mut value) in rws_incomplete_or_dependent_tx_map {
            final_tx_order.append(&mut value);
        }

        // set tx id as the index in the block
        self.set_tx_idx_by_position_in_block(&mut final_tx_order);

        final_tx_order
    }

    /// Get the RWS given an input message for some contract.
    /// Fetches the SE profile, parses it & gets the final RWS in form of keys as bytes
    /// It returns a vec where each item contains the contract address as well as all the keys
    /// it will touch
    /// The return vector maintains the original transaction order.
    #[cfg(not(feature = "tx_reordering"))]
    fn get_original_ordered_rws(&self, block: Block) -> Vec<RWSContext> {
        let mut rws = vec![];

        self.save_rws(
            block,
            |tx| rws.push(tx)
        );

        self.set_tx_idx_by_position_in_block(&mut rws);
        rws
    }


    /// Given a block, parses each tx in the block, and evaluates it given the inputs for that tx, and
    /// the current storage state to get the RWS for each tx in the block.
    /// It uses the ```save_rws``` function to save the RWS in a customized way. The saved RWS state is stored
    /// in the caller. THis function is only responsible for the actual getting of the RWS for the txs.
    /// The ordering of the RWS is done in the caller.
    fn save_rws<F>(&self, block: Block, mut save_rws: F)
    where
        F: FnMut(RWSContext),
    {

        // this is different from the instantiation count from state_manager. This is just a mock.
        // We don't actually instantiate. And here we do it best case scenario - we assume every instantiaion
        // will 'work', and assign it a different SC address. We use this to get a unique address fo reach 
        // instantiation - to guarantee no conflicts between operations on the instantiated contract.
        let mut instantiation_counts: HashMap<u128, u128> = HashMap::new();

        for msg in block.into_iter() {
            let tx = match msg {
                VMMessage::Instantiation { 
                    ref message, 
                    contract_code_id,
                    ..
                } => {
                    // Increase instantiation count for each instantiate for the same code id
                    let instantiation_count = if let Some(count) = instantiation_counts.get_mut(&contract_code_id) {
                            *count += 1;
                            *count
                        }
                        else {
                            instantiation_counts.insert(contract_code_id, 0);
                            0
                    };
                        
                    let profile = self.state_manager.read().unwrap().get_profile(contract_code_id);
                    let mut context = self.get_rws_instantiation(profile, message.as_slice(), 
                        contract_code_id, instantiation_count);
                    context.tx_message = Some(msg);
                    context
                },

                VMMessage::Invocation { 
                    ref message, // ref is used not to move this field. Else, we would not be able to move it into the Some(msg) below
                    ref entry_point,
                    ref contract_address, 
                    ..
                } => {
                    let profile = self.state_manager.read().unwrap().get_profile_by_address(contract_address);
                    match &self.state_manager.read().unwrap().get_sc_storage(contract_address) {
                        Some(state) => { 
                            // Build mock depsMut
                            let mut context = self.get_rws_for_invocation(
                                                        &entry_point, profile, message.as_slice(), contract_address, &state.storage);
                            context.tx_message = Some(msg);
                            context
                        }
                        // If invocation on a contract that wasn't yet instantiated
                        None => panic!("Invoquing execution on a contract that wasn't instantiated yet!")
                    }
                },
                _ => todo!()
            };

            save_rws(tx);
        };
    }




    fn set_tx_idx_by_position_in_block(&self, txs: &mut Vec<RWSContext>) {
        for (idx, el) in txs.iter_mut().enumerate() {
            el.tx_block_id = idx as TxId;
        }
    }


    fn get_rws_instantiation(&self, profile: Arc<SCProfile>, message: &[u8], contract_code_id: u128, instantiation_count: u128) -> RWSContext {
        let querier = cosmwasm_std::testing::MockQuerier::default();
        let mut_deps = DepsMut { 
            storage: &S::new(), // creates empty storage for instantiates
            api: &cosmwasm_std::testing::MockApi::default(), 
            querier: cosmwasm_std::QuerierWrapper::new( &querier)
        };

        // set the contract's address given the predefined address from the trace
        let address = (self.address_mapper)(
            contract_code_id, 
            instantiation_count
        );

        RWSContext {
            rws: self.symb_exec_engine.get_rws_instantiate(&profile, &mut_deps, message),
            address: address,
            tx_message: None, // will be set by calling function
            tx_block_id: 0,   // will be set by calling function
        }
    }

    fn get_rws_for_invocation(&self, entry_point: &InstantiatedEntryPoint, profile: Arc<SCProfile>, message: &[u8],
        contract_address: &ScAddr, storage: &Arc<S>) -> RWSContext
    {
        let querier = cosmwasm_std::testing::MockQuerier::default();
        let mut_deps = DepsMut { 
            storage: &**storage,
            api: &cosmwasm_std::testing::MockApi::default(), 
            querier: cosmwasm_std::QuerierWrapper::new( &querier)
        };
        match entry_point {
            InstantiatedEntryPoint::Execute => 
                RWSContext {
                    rws: self.symb_exec_engine.get_rws_execute(&profile, &mut_deps, message),
                    address: *contract_address,
                    tx_message: None, // will be set by calling function
                    tx_block_id: 0,   // will be set by calling function
                },
            InstantiatedEntryPoint::Query   => {
                RWSContext {
                    rws: self.symb_exec_engine.get_rws_query(&profile, &mut_deps, message),
                    address: *contract_address,
                    tx_message: None, // will be set by calling function
                    tx_block_id: 0,   // will be set by calling function
                }
            },
            InstantiatedEntryPoint::Migrate => todo!("MIgrate not implemented"),
        }
    }

    fn get_execution_context(&self) -> ThreadExecutionContext<A, S, W, Q, E> {
        ThreadExecutionContext {
            state_manager: Arc::clone(&self.state_manager),
            backend_builder: Arc::clone(&self.backend_builder),
            concurrent_backend_builder: Arc::clone(&self.concurrent_backend_builder),
            max_concurrent_vms: self.max_concurrent_instances,
        }
    }

    #[allow(unused_variables)]
    fn execute_block(&mut self, rws: Vec<RWSContext>, schedule: ConcurrentSchedule, batch_type: BatchType ) -> std::io::Result<Vec<String>> {
        #[cfg(feature = "exec_time")] // Only count tx invocation (after the VMs are instantiated)
        if batch_type == BatchType::Invocation { self.start_schedule_execution_timer();  }
        else                                  { self.start_instantiation_calls_timer(); }

        let mut handles = vec![];
        let resps = Arc::new(Mutex::new(vec![]));
        let schedule = Arc::new(schedule);
        let rws = Arc::new(rws);
        let thread_exec_ctx = Arc::new(VMManager::get_execution_context(&self));

        // not included in execution time
        #[cfg(feature = "debug_graph")]
        {
            let suffix = if batchType == BatchType::Instantiation { "instantiation".to_owned() } else { "execution".to_owned() };
            let graph_name = format!("{:?}_{:?}_before", self.block_number, suffix);
            schedule.generate_debug_graph(graph_name, &rws);
        }

        // execute each message
        for i in 0..self.n_threads {
            let schedule_ref = Arc::clone(&schedule);
            let resps_ref = Arc::clone(&resps);
            let rws_ref = Arc::clone(&rws);
            let thread_exec_ctx_ref = Arc::clone(&thread_exec_ctx);

            let handle = thread::spawn(move || {
                loop {

                    #[cfg(feature = "debug")]
                    print_with_thread_id!("Waiting for message to execute");

                    if let Some(tx_id) = &schedule_ref.get_next_message_to_execute() {
                        
                        #[cfg(feature = "debug")]
                        print_with_thread_id!("Executing {:?}", tx_id);

                        // TODO - try using raw pointer as below.. - was giving invalida memory reference error
                        // move out the data for current tx
                        // let message = unsafe { rws_ref.as_ptr().offset(*tx_id as isize).read() };
                        let message = rws_ref[*tx_id as usize].clone();

                        // let message = rws_ref[*tx_id as usize] as *mut RWSContext;
                        // TODO - below clone should be optimized - no need.. we can pass a reference, or just return the same arc from the method
                        let resp = VMManager::<A, S, W, Q, E>::execute_message(
                            Arc::clone(&schedule_ref), 
                            &*thread_exec_ctx_ref, 
                            message, 
                            *tx_id);
                        resps_ref.lock().push(resp);
                    }
                    else {

                        #[cfg(feature = "debug")]
                        print_with_thread_id!("Finished executing");

                        break; 
                    }
                }
            });

            handles.push(handle);
        }

        // wait for all threads
        for handle in handles {
            handle.join().unwrap();
        }

        #[cfg(feature = "exec_time")]
        if batch_type == BatchType::Invocation { self.stop_schedule_execution_timer();  }
        else                                  { self.stop_instantiation_calls_timer(); }


        #[cfg(feature = "exec_time")]
        self.start_schedule_persistence_timer();

        self.persist_schedule(&schedule);
        
        #[cfg(feature = "exec_time")]
        self.stop_schedule_persistence_timer();


        // not included in execution time
        #[cfg(feature = "debug_graph")]
        {
            let suffix = if batch_type == BatchType::Instantiation { "instantiation".to_owned() } else { "execution".to_owned() };
            let graph_name = format!("{:?}_{:?}_after", self.block_number, suffix);
            schedule.generate_debug_graph(graph_name, &rws);
        }


        // return the response vector contents
        let mut guard = resps.lock();
        Ok(std::mem::take(&mut *guard))
    }

    fn persist_schedule(&self, concurrent_schedule: &Arc<ConcurrentSchedule>) {
        let sc_storage_manager_lock = self.state_manager.read().unwrap();
        concurrent_schedule.persist_schedule(&*sc_storage_manager_lock);
    }

    fn execute_message(schedule: Arc<ConcurrentSchedule>, thread_exec_context: &ThreadExecutionContext<A, S, W, Q, E>, 
        msg: RWSContext, tx_id: TxId) -> String {
        // TODO - try passing a reference here -> we need to change later on the backend and mocksStorage to handle references instead of
        // Vec. Cloning the entire RWS is very innefficient here..
        let rws = msg.rws.rws;

        let response = match &msg.tx_message {
            Some(VMMessage::Instantiation { 
                message, 
                contract_code_id,
                ..
            }) => VMManager::<A, S, W, Q, E>::compile_instantiate_vm(msg.tx_block_id, &msg.address, Arc::clone(&schedule), 
                &thread_exec_context, *contract_code_id, message.as_slice(), rws).unwrap(),

            Some(VMMessage::Invocation {
                message, 
                entry_point,
                contract_address, 
                ..
            }) => match entry_point {
                InstantiatedEntryPoint::Execute => VMManager::<A, S, W, Q, E>::instantiate_vm(msg.tx_block_id, Arc::clone(&schedule),  
                    &thread_exec_context, contract_address, message.as_slice(), rws, VMCall::Execute ).unwrap(),
                InstantiatedEntryPoint::Query   => VMManager::<A, S, W, Q, E>::instantiate_vm(msg.tx_block_id, Arc::clone(&schedule), 
                    &thread_exec_context, contract_address, message.as_slice(), rws, VMCall::Query   ).unwrap(),
                // InstantiatedEntryPoint::Reply => String::from(""),
                InstantiatedEntryPoint::Migrate => todo!("Migrate not implemented"),
            },
            Some(t) => todo!("VMMessage type not implemented: {:?}", t),
            None => unreachable!("RWSContext doesn't have a message set during block execution!"), // Should never happen
        };

        schedule.on_tx_finish(msg.tx_block_id);

        response
    }

    /// Used on contract instantiations to compile the code
    fn compile_instantiate_vm(tx_block_id: TxId, address: &ScAddr, schedule: Arc<ConcurrentSchedule>, thread_exec_context: &ThreadExecutionContext<A, S, W, Q, E>, 
            contract_code_id: u128, msg: &[u8], rws: Vec<ReadWrite>) -> std::io::Result<String> {

        // Get SC code by ID & set the mapping address -> code_id for future invocations on it
        let state_manager_lock = thread_exec_context.state_manager.read().unwrap();
        let code = state_manager_lock.get_code(contract_code_id)?;
        state_manager_lock.link_address_to_code(contract_code_id, address);
        drop(state_manager_lock);

        let partitioned_storage = Arc::new(S::new());
        let backend = Arc::new((thread_exec_context.backend_builder)(partitioned_storage));

        // initializes N VMs for each different SC
        let mut instances = vec![];
        for _ in 0..thread_exec_context.max_concurrent_vms {
            // build runtime information to execute
            let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
            let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
            let module = Arc::new(compile( &engine, code.as_slice()).unwrap());
            let store = Store::new(engine);
            
            // TODO - start with an empty or default concurrent backend with minimal allocation/overhead
            let concurrent_backend: ConcurrentBackend<A, W, Q> = (thread_exec_context.concurrent_backend_builder)(tx_block_id, Arc::clone(&schedule),
                Arc::clone(&backend), &address, vec![]);

            let instance = instance_from_module(
                store, 
                &module, 
                concurrent_backend, 
                much_gas.gas_limit, 
                None).unwrap();
            
            instances.push(instance);
        }

        let state_manager = thread_exec_context.state_manager.read().unwrap();
        // save instance
        state_manager.save_instance(
            contract_code_id,
            *address,
            Arc::clone(&backend),
            instances);

        let concurrent_backend: ConcurrentBackend<A, W, Q> = (thread_exec_context.concurrent_backend_builder)(tx_block_id, schedule,
            backend, &address, rws);

        state_manager.execute_instance(address, concurrent_backend, tx_block_id, |instance| {
            let resp = call_instantiate::<_, _, _, Empty>(
                instance, 
                &mock_env(), 
                &mock_info("", &[]), 
                msg
            ).unwrap().unwrap();
            Ok(format!("{:?}", resp))
        })
    }

    /// Used to instantiate an already deployed/compiled contract with 
    /// already created storage
    fn instantiate_vm(tx_block_id: TxId,  schedule: Arc<ConcurrentSchedule>, thread_exec_context: &ThreadExecutionContext<A, S, W, Q, E>, contract_address: &ScAddr, 
        message: &[u8], rws: Vec<ReadWrite>, call_type: VMCall) -> std::io::Result<String> {

        #[cfg(feature = "debug")]
        print_with_thread_id!("Calling execute in VM");

        let storage = thread_exec_context.state_manager.read().unwrap().get_sc_storage(contract_address).unwrap();

        let concurrent_backend: ConcurrentBackend<A, W, Q> = (thread_exec_context.concurrent_backend_builder)(tx_block_id, schedule,
            storage, &contract_address, rws);

        let state_manager = thread_exec_context.state_manager.read().unwrap();
        
        state_manager.execute_instance(contract_address, concurrent_backend, tx_block_id, |instance| {
            match call_type {
                VMCall::Execute => {
                    let resp = call_execute::<_, _, _, Empty>(instance, &mock_env(), &mock_info("", &[]), message)
                        .unwrap().unwrap();
                    Ok(format!("{:?}", resp))
                },
                VMCall::Query => {
                    let resp = call_query::<_, _, _>(instance, &mock_env(), message)
                        .unwrap().unwrap();
                    Ok(String::from_utf8(base64::decode(resp.to_string()).unwrap()).unwrap())
                },
            }
        })
    }
}


#[cfg(test)]
mod tests {
    use std::{collections::HashMap, sync::{Arc, RwLock}};

    use cosmwasm_std::Empty;
    use serial_test::serial;
    use wasmer::Store;

    use crate::{
        backend::ConcurrentBackend, call_execute, call_instantiate, internals::instance_from_module, 
        symb_exec::{Commutativity, Key, ReadWrite, StorageDependency, SymbolicExecutionEngine, TxRWS}, 
        testing::{mock_concurrent_backend, mock_env, mock_info, mock_persistent_backend, mock_tx_operation, 
            MockApi, MockConcurrentStorage, MockQuerier, MockStorageWrapper
        }, 
        vm_manager::{
            schedule::{ScAddr, ADDR_SIZE}, serial_schedule::ScheduleBuilder, vm_manager::{RWSContext, VMCall, DEFAULT_MEMORY_LIMIT, HIGH_GAS_LIMIT}
        }, 
        wasm_backend::{compile, make_compiling_engine}, 
        ConcurrentSchedule, InstanceOptions, InstantiatedEntryPoint, 
        SCManager, SEStatus, VMMessage
    };

    use super::{AddressMapper, BackendBuilder, ConcurrentBackendBuilder, VMManager};

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");

    const SC_ADDR_A: ScAddr = *b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const SC_ADDR_B: ScAddr = *b"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    const SC_ADDR_C: ScAddr = *b"cccccccccccccccccccccccccccccccc";
    const SC_ADDR_D: ScAddr = *b"dddddddddddddddddddddddddddddddd";


    fn mock_backend_builder() -> Arc<BackendBuilder<MockApi, MockConcurrentStorage, MockQuerier>> {
        Arc::new(|storage| {
            mock_persistent_backend(&[], storage)
        })
    }

    fn mock_concurrent_backend_builder() -> Arc<ConcurrentBackendBuilder<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier>> {
        Arc::new(|tx_block_id, concurrent_schedule, backend, sc_address, rws| {
            ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(tx_block_id, concurrent_schedule, backend, sc_address, rws)
        })
    }

    fn mock_address_mapper() -> Arc<AddressMapper> {
        let mut mapping: HashMap<u128, HashMap<u128, ScAddr>> = HashMap::from([(0, HashMap::new())]);
        mapping.get_mut(&0).unwrap().insert(0, SC_ADDR_A);
        mapping.get_mut(&0).unwrap().insert(1, SC_ADDR_B);
        mapping.get_mut(&0).unwrap().insert(2, SC_ADDR_C);
        mapping.get_mut(&0).unwrap().insert(3, SC_ADDR_D);

        Arc::new(move |contract_code_id: u128, instantiation: u128| {
            mapping.get(&contract_code_id).unwrap().get(&instantiation).unwrap().clone()
        })
    }

    fn mock_vm_manager(n_threads: u16, n_instances_per_sc: u16,  address_mapper: Arc<AddressMapper>) -> VMManager<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier, SymbolicExecutionEngine> {
        let se_engine = Arc::new(SymbolicExecutionEngine::new());
        let state_manager = SCManager::new(Arc::clone(&se_engine));
        // simulate installing a contract
        state_manager.save_code(CONTRACT, None).unwrap();

        let state_manager = Arc::new(RwLock::new(state_manager));
        VMManager::new(
            Arc::clone(&state_manager), 
            Arc::clone(&address_mapper),
            mock_backend_builder(),
            mock_concurrent_backend_builder(),
            n_threads,
            n_instances_per_sc
        )
    }

    #[test]
    #[serial]
    fn address_mapper() {
        let se_engine = Arc::new(SymbolicExecutionEngine::new());
        let state_manager = SCManager::new(Arc::clone(&se_engine));
        let mut mapping: HashMap<u128, HashMap<u128, ScAddr>> = HashMap::from([
            (0, HashMap::new()),
            (1, HashMap::new())
        ]);

        mapping.get_mut(&0).unwrap().insert(0, SC_ADDR_A);
        mapping.get_mut(&0).unwrap().insert(1, SC_ADDR_B);
        mapping.get_mut(&1).unwrap().insert(0, SC_ADDR_C);
        mapping.get_mut(&1).unwrap().insert(1, SC_ADDR_D);

        let address_mapper = move |contract_code_id: u128, instantiation: u128| {
            mapping.get(&contract_code_id).unwrap().get(&instantiation).unwrap().clone()
        };



        let vm_manager = VMManager::new(
            Arc::new(RwLock::new(state_manager)), 
            Arc::new(address_mapper),
            mock_backend_builder(),
            mock_concurrent_backend_builder(),
            1,
            1
        );

        assert_eq!((vm_manager.address_mapper)(0, 0), SC_ADDR_A);
        assert_eq!((vm_manager.address_mapper)(0, 1), SC_ADDR_B);
        assert_eq!((vm_manager.address_mapper)(1, 0), SC_ADDR_C);
        assert_eq!((vm_manager.address_mapper)(1, 1), SC_ADDR_D);
    }

    #[ignore]
    #[test]
    #[serial]
    fn vanilla_instantiation_and_execution() {
        // save initial code -> will have code_id = 0
        let state_manager = SCManager::new(Arc::new(SymbolicExecutionEngine::new()));
        state_manager.save_code(CONTRACT, None).unwrap();

        assert_eq!(state_manager.get_code(0).unwrap(), CONTRACT);
        
        // Create the compiled module & storage
        let code = state_manager.get_code(0).unwrap();
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        let module = compile( &engine, code.as_slice()).unwrap();
        let concurrent_storage = Arc::new(MockConcurrentStorage::default());
        let backend = Arc::new(mock_persistent_backend(&[], Arc::clone(&concurrent_storage)));

        let concurrent_backend = mock_concurrent_backend(&[], concurrent_storage);

        let store = Store::new(engine);
        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
        let instance = instance_from_module(store, &module, concurrent_backend, much_gas.gas_limit, None).unwrap();
        let instances = vec![instance];

        // save instance
        state_manager.save_instance(
            0,
            SC_ADDR_A,
            Arc::clone(&backend),
            instances);

        let rws = vec![];
        
        // schedule needs at least 1 operation to know the tx
        let mut schedule = ScheduleBuilder::new();
        schedule.build_from_rws(&mut vec![
            mock_tx_operation(SC_ADDR_A, &vec![1u8], 0, ReadWrite::write(), Commutativity::NonCommutative)
        ]);
        let concurrent_schedule = Arc::new(ConcurrentSchedule::from_schedule_builder(schedule, 1));


        // instantiate

        let concurrent_backend = ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(0, Arc::clone(&concurrent_schedule),
            Arc::clone(&backend), &SC_ADDR_A, rws);

        let msg = br#"{}"#;
        let contract_res = state_manager.execute_instance(&SC_ADDR_A, concurrent_backend, 0, |instance| {
            let c = call_instantiate::<_, _, _, Empty>(
                instance, 
                &mock_env(), 
                &mock_info("", &[]), 
                msg
            ).unwrap().unwrap();
            Ok(format!("{:?}", c))
        });

        assert_eq!(contract_res.unwrap(), "Response { messages: [], attributes: [], events: [], data: None }".to_owned());
        assert_eq!(state_manager.get_instantiation_count(0), 1);


        // execute

        let msg = br#"{
            "AddOne": { 
                "user": "ADMIN"
            }
        }"#;
        let concurrent_backend = ConcurrentBackend::<MockApi, MockStorageWrapper, MockQuerier>::new(0, Arc::clone(&concurrent_schedule),
            Arc::clone(&backend), &SC_ADDR_A, vec![]);
        let contract_res = state_manager.execute_instance(&SC_ADDR_A, concurrent_backend, 0, |instance| {
            let c = call_execute::<_, _, _, Empty>(
                instance, 
                &mock_env(), 
                &mock_info("", &[]), 
                msg
            ).unwrap().unwrap();
            Ok(format!("{:?}", c))
        });

        assert_eq!(contract_res.unwrap(), "Response { messages: [], attributes: [], events: [], data: None }".to_owned());
        assert_eq!(state_manager.get_instantiation_count(0), 1);


        state_manager.cleanup();
    }


    #[ignore]
    #[test]
    #[serial]
    fn vanilla_sequential_instantiate_vm() {
        let vm_manager = mock_vm_manager(1, 1, mock_address_mapper());

        let msg = br#"{}"#;
        let thread_ctx = vm_manager.get_execution_context();
        
        // schedule needs at least 1 operation to know the tx
        let mut schedule = ScheduleBuilder::new();
        let rws = mock_tx_operation(SC_ADDR_A, &vec![0, 4, 98, 97, 110, 65, 68, 77, 73, 78], 0, ReadWrite::write(), Commutativity::NonCommutative);
        schedule.build_from_rws(&mut vec![
            rws.clone()
        ]);

        let resp = VMManager::<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier, SymbolicExecutionEngine>::compile_instantiate_vm(
            0, 
            &SC_ADDR_A, 
            Arc::new(ConcurrentSchedule::from_schedule_builder(schedule, 1)), 
            &thread_ctx, 
            0, 
            msg, 
            rws.rws.rws
        ).unwrap();
        assert_eq!("Response { messages: [], attributes: [], events: [], data: None }", resp);

        vm_manager.state_manager.read().unwrap().cleanup();
    }
    
    #[ignore]
    #[test]
    #[serial]
    fn vanilla_sequential_execute_vm_untracked_operations() {
        let vm_manager = mock_vm_manager(1, 1, mock_address_mapper());
        let mut schedule = ScheduleBuilder::new();
        let sc_address = SC_ADDR_A; // needs to be "a" since this is the address created by the mock_vm_manager()

        // every tx needs to be detected when building the schedule. So we need a random operation for it to be detected
        schedule.build_from_rws(&mut vec![
            mock_tx_operation(SC_ADDR_A, &vec![1u8], 0, ReadWrite::write(), Commutativity::NonCommutative)
        ]);

        let schedule = Arc::new(ConcurrentSchedule::from_schedule_builder(schedule, 1));

        let msg = br#"{}"#;
        let thread_ctx = vm_manager.get_execution_context();
        let resp = VMManager::<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier, SymbolicExecutionEngine>::compile_instantiate_vm(0, &SC_ADDR_A, Arc::clone(&schedule), &thread_ctx, 0, msg, vec![]).unwrap();
        assert_eq!("Response { messages: [], attributes: [], events: [], data: None }", resp);

        let msg = br#"{
            "AddOne": {
                "user": "ADMIN"
            }
        }"#;
        let thread_ctx = vm_manager.get_execution_context();
        let resp = VMManager::<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier, SymbolicExecutionEngine>::instantiate_vm(0, Arc::clone(&schedule), &thread_ctx, &sc_address, msg, 
        vec![], VMCall::Execute).unwrap();
        assert_eq!("Response { messages: [], attributes: [], events: [], data: None }", resp);

        vm_manager.state_manager.read().unwrap().cleanup();
    }

    #[ignore]
    #[test]
    #[serial]
    fn sequential_query_vm() {
        let vm_manager: VMManager<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier, SymbolicExecutionEngine> = mock_vm_manager(1, 1, mock_address_mapper());

        let msg = br#"{}"#;
        let thread_ctx = vm_manager.get_execution_context();

        // schedule needs at least 1 operation to know the tx
        let mut schedule = ScheduleBuilder::new();
        schedule.build_from_rws(&mut vec![
            mock_tx_operation(SC_ADDR_A, &vec![1u8], 0, ReadWrite::write(), Commutativity::NonCommutative)
        ]);
        let schedule = Arc::new(ConcurrentSchedule::from_schedule_builder(schedule, 1));

        let resp = VMManager::<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier, SymbolicExecutionEngine>::compile_instantiate_vm(0, &SC_ADDR_A, Arc::clone(&schedule),  &thread_ctx, 0, msg, vec![]).unwrap();
        assert_eq!("Response { messages: [], attributes: [], events: [], data: None }", resp);

        let msg = br#"{
            "GetBalance": {
                "user": "ADMIN"
            }
        }"#;
        let resp = VMManager::<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier, SymbolicExecutionEngine>::instantiate_vm(0, Arc::clone(&schedule), &thread_ctx, &SC_ADDR_A, msg,  
            vec![], VMCall::Query).unwrap();
        assert_eq!("{\"balance\":1000}", resp);

        vm_manager.state_manager.read().unwrap().cleanup();
        
    }



    #[test]
    #[serial]
    fn get_rws() {
        let mut vm_manager = mock_vm_manager(1, 1, mock_address_mapper());

        let msgs = vec![
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                reply: None,
                hash: "".to_owned(),
                label: "".to_owned(),
            },
        ];

        // instantiate first, to create storage
        vm_manager.handle_block(msgs).unwrap();

        // only after having storage created
        let vm_message = VMMessage::Invocation {
            entry_point: InstantiatedEntryPoint::Execute,
            contract_address: SC_ADDR_A,
            message: br#"{
                "AddOne": {
                    "user": "ADMIN"
                }
            }"#.to_vec(),
            funds: vec![],
            sender: "".to_owned(),
            hash: "".to_owned(),
        };
        let msgs = vec![
            vm_message.clone()
        ];

        let rws = vm_manager.get_ordered_rws(msgs);
        assert_eq!(
            rws,
            vec![RWSContext {
                address: SC_ADDR_A,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "A".to_owned(),
                    rws: vec![
                        ReadWrite::Read {
                            storage_dependency: StorageDependency::Independent,
                            key: Key::Bytes(vec![0, 4, 98, 97, 110, 107, 65, 68, 77, 73, 78]),
                            commutativity: Commutativity::Commutative,
                            operation_node: None,
                        },
                        ReadWrite::Write {
                            storage_dependency: StorageDependency::Independent,
                            key: Key::Bytes(vec![0, 4, 98, 97, 110, 107, 65, 68, 77, 73, 78]),
                            commutativity: Commutativity::Commutative,
                            operation_node: None,
                        },
                    ]
                },
                tx_message: Some(vm_message),
                tx_block_id: 0,
            }]
        );
        
        vm_manager.state_manager.read().unwrap().cleanup();
    }


    #[test]
    #[serial]
    fn sequential_persistent_calls() {
        let mut vm_manager = mock_vm_manager(1, 1, mock_address_mapper());

        let msgs = vec![
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                reply: None,
                hash: "".to_owned(),
                label: "".to_owned(),
            },
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                reply: None,
                hash: "".to_owned(),
                label: "".to_owned(),
            },
        ];

        // We ordered this by order of the scheduled execution. 
        // Internally, there will be a reordering, placing all txs
        // with the same RWS together. So even if we placed a Query in between
        // the executes, all queries would be ordered to be executed after the executes.
        let invocations = vec![
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "AddOne": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_B,
                message: br#"{
                    "AddOne": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "AddOne": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "AddUser": {
                        "admin": "Balelas"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "GetBalance": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_B,
                message: br#"{
                    "GetBalance": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "GetBalance": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "GetBalance": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },

        ];

        vm_manager.handle_block(msgs).unwrap();
        let resps = vm_manager.handle_block(invocations).unwrap();

        assert_eq!("Response { messages: [], attributes: [], events: [], data: None }", resps[0]);
        assert_eq!("Response { messages: [], attributes: [], events: [], data: None }", resps[1]);
        assert_eq!("Response { messages: [], attributes: [], events: [], data: None }", resps[2]);
        assert_eq!("Response { messages: [], attributes: [], events: [], data: None }", resps[3]);

        // this is the query for SC B - as the execute of it is in 2nd place, it pushes first its dependencies
        // before the executes of SC A
        assert_eq!("{\"balance\":1001}", resps[4]);
        // these are the queries for SC A
        assert_eq!("{\"balance\":1002}", resps[5]);
        assert_eq!("{\"balance\":1002}", resps[6]);
        assert_eq!("{\"balance\":1002}", resps[7]);

        vm_manager.state_manager.read().unwrap().cleanup();

    }



    #[test]
    #[serial]
    fn parallel_workload_test() {
        let mut vm_manager = mock_vm_manager(2, 2, mock_address_mapper());

        let invocations = vec![
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "GetBalance": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "AddOne": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_B,
                message: br#"{
                    "AddOne": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_C,
                message: br#"{
                    "AddOne": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_D,
                message: br#"{
                    "AddOne": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "AddUser": {
                        "admin": "Balelas"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_B,
                message: br#"{
                    "GetBalance": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_D,
                message: br#"{
                    "AddOne": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "GetBalance": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_C,
                message: br#"{
                    "GetBalance": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Execute,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "AddOne": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_A,
                message: br#"{
                    "GetBalance": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            VMMessage::Invocation {
                entry_point: InstantiatedEntryPoint::Query,
                contract_address: SC_ADDR_D,
                message: br#"{
                    "GetBalance": {
                        "user": "ADMIN"
                    }
                }"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                hash: "".to_owned(),
            },
            // notice that instantiation order does not matter - we always place all instantiations at the beginning
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                reply: None,
                hash: "".to_owned(),
                label: "".to_owned(),
            },
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                reply: None,
                hash: "".to_owned(),
                label: "".to_owned(),
            },
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                reply: None,
                hash: "".to_owned(),
                label: "".to_owned(),
            },
            VMMessage::Instantiation {
                contract_code_id: 0,
                message: br#"{}"#.to_vec(),
                funds: vec![],
                sender: "".to_owned(),
                reply: None,
                hash: "".to_owned(),
                label: "".to_owned(),
            },
        ];

        vm_manager.handle_block(invocations).unwrap();


        // // 1 query at a time to enforce serializability to allow comparing received response with predicted
        // let invocation = vec![
        //     VMMessage::Invocation {
        //         entry_point: InstantiatedEntryPoint::Query,
        //         contract_address: SC_ADDR_A,
        //         message: br#"{
        //             "GetBalance": {
        //                 "user": "ADMIN"
        //             }
        //         }"#.to_vec(),
        //         code_id: 0,
        //     },
        // ];
        // let resp = vm_manager.handle_block(invocation).unwrap();
        // assert_eq!("{\"balance\":1002}", resp[0]);


        // // 1 query at a time to enforce serializability to allow comparing received response with predicted
        // let invocation = vec![
        //     VMMessage::Invocation {
        //         entry_point: InstantiatedEntryPoint::Query,
        //         contract_address: SC_ADDR_B,
        //         message: br#"{
        //             "GetBalance": {
        //                 "user": "ADMIN"
        //             }
        //         }"#.to_vec(),
        //         code_id: 0,
        //     },
        // ];
        // let resp = vm_manager.handle_block(invocation).unwrap();
        // assert_eq!("{\"balance\":1001}", resp[0]);

        // let invocation = vec![
        //     VMMessage::Invocation {
        //         entry_point: InstantiatedEntryPoint::Query,
        //         contract_address: SC_ADDR_C,
        //         message: br#"{
        //             "GetBalance": {
        //                 "user": "ADMIN"
        //             }
        //         }"#.to_vec(),
        //         code_id: 0,
        //     },
        // ];
        // let resp = vm_manager.handle_block(invocation).unwrap();
        // assert_eq!("{\"balance\":1001}", resp[0]);

        // let invocation = vec![
        //     VMMessage::Invocation {
        //         entry_point: InstantiatedEntryPoint::Query,
        //         contract_address: SC_ADDR_D,
        //         message: br#"{
        //             "GetBalance": {
        //                 "user": "ADMIN"
        //             }
        //         }"#.to_vec(),
        //         code_id: 0,
        //     },
        // ];
        // let resp = vm_manager.handle_block(invocation).unwrap();
        // assert_eq!("{\"balance\":1002}", resp[0]);

        vm_manager.state_manager.read().unwrap().cleanup();

    }

    #[test]
    #[serial]
    fn full_parallel_workload_100_txs() {

        let mut mapping: HashMap<u128, HashMap<u128, ScAddr>> = HashMap::from([(0, HashMap::new())]);
        let n_contracts = 100;

        for i in 0..n_contracts {
            mapping.get_mut(&0).unwrap().insert(i, [i as u8; ADDR_SIZE]);
        }
    
        let addr_mapping = Arc::new(move |contract_code_id: u128, instantiation: u128| {
            mapping.get(&contract_code_id).unwrap().get(&instantiation).unwrap().clone()
        });

        let mut vm_manager = mock_vm_manager(4, 3, addr_mapping);
        let mut msgs = vec![];

        // instantiations
        for _ in 0..n_contracts {
            msgs.push(
                VMMessage::Instantiation {
                    contract_code_id: 0,
                    message: br#"{}"#.to_vec(),
                    funds: vec![],
                    sender: "".to_owned(),
                    reply: None,
                    hash: "".to_owned(),
                    label: "".to_owned(),
                }
            );
        }

        for i in 0..n_contracts {
            // 2 sequential increments per contract
            msgs.push(
                VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: [i as u8; ADDR_SIZE],
                    message: br#"{
                        "AddOne": {
                            "user": "ADMIN"
                        }
                    }"#.to_vec(),
                    funds: vec![],
                    sender: "".to_owned(),
                    hash: "".to_owned(),
                }
            );
            msgs.push(
                VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: [i as u8; ADDR_SIZE],
                    message: br#"{
                        "AddOne": {
                            "user": "ADMIN"
                        }
                    }"#.to_vec(),
                    funds: vec![],
                    sender: "".to_owned(),
                    hash: "".to_owned(),
                }
            );
        }

        vm_manager.handle_block(msgs).unwrap();

        vm_manager.state_manager.read().unwrap().cleanup();
    }

}