use std::{
    collections::{HashSet, VecDeque}, sync::{atomic::{AtomicUsize, Ordering}, Arc},
};

use dashmap::DashSet;
use parking_lot::{Mutex, Condvar};

use crate::{
    symb_exec::{Commutativity, ProfileGenerator}, testing::{ConcurrentStorage, StorageWrapper}, vm_manager::schedule::MergeableValue, BackendApi, Querier, SCManager
};

use super::{
    sc_storage::ConcurrentTimer, schedule::{NodeRef, OpType, SCSchedule, ScAddr, TxId, VecOperation}, serial_schedule::{ScheduleBuilder, SerialQueues}, LastWrites, Schedule
};

#[cfg(feature = "debug_graph")]
use super::{dot_schedule::{DotSchedule, NodeColor}, RWSContext};
#[cfg(feature = "exec_time")]
use std::time::{Duration, Instant};
#[cfg(feature = "debug")]
use crate::print_with_thread_id;

#[derive(Debug)]
pub struct ConcurrentQueues {
    executed_txs: Mutex<TxId>,

    total_txs: TxId,

    ready_queue: DashSet<TxId>,
    partial_ready_queue: DashSet<TxId>,

    cvar: Condvar,
}

impl PartialEq for ConcurrentQueues {
    fn eq(&self, other: &Self) -> bool {
        *self.executed_txs.lock() ==  *other.executed_txs.lock() &&
        self.total_txs == other.total_txs //&&
        // *self.ready_queue.lock() == *other.ready_queue.lock() &&
        // *self.partial_ready_queue.lock() == *other.partial_ready_queue.lock()
    }
}

impl ConcurrentQueues {
    fn new() -> ConcurrentQueues {
        ConcurrentQueues {
            executed_txs: Mutex::new(0),

            total_txs: 0,

            ready_queue: DashSet::new(),
            partial_ready_queue: DashSet::new(),
        
            cvar: Condvar::new(),
        }
    }

    fn from_serial_queues(serial_queues: SerialQueues) -> ConcurrentQueues {
        ConcurrentQueues {
            executed_txs: Mutex::new(serial_queues.executed_txs),
            total_txs: serial_queues.total_txs,
            ready_queue: DashSet::from_iter(serial_queues.ready_queue.into_iter()),
            partial_ready_queue: DashSet::from_iter(serial_queues.partial_ready_queue.into_iter()),
            cvar: Condvar::new(),
        }
    }

    /// Pushes to both queues and signals waiting threads if needed.
    /// Should only be called after the tx has finished execution, as this method
    /// increases an internal counter that tracks the number of executed txs
    fn push_and_signal(&self, ready: Vec<TxId>, partial_ready: Vec<TxId>) {
        // let total_txs = ready.len() + partial_ready.len();

        let mut total_txs = 0;

        for tx in ready {
            // if self.tx_states[tx] == TxState::NotExecuted {
                total_txs += 1;
                self.ready_queue.insert(tx);
                self.partial_ready_queue.remove(&tx);
            // }
        }
        
        for tx in partial_ready {
            // if self.tx_states[tx] == TxState::NotExecuted {
                total_txs += 1;
                self.partial_ready_queue.insert(tx);
            // }
        }

        let mut lock = self.executed_txs.lock();
        *lock += 1;
        let has_messages_to_execute = *lock < self.total_txs;
        drop(lock);

        if total_txs == 0 && !has_messages_to_execute { 
            self.cvar.notify_all(); 
        } else if total_txs == 2 { 
            self.cvar.notify_one(); 
        } else if total_txs > 2 { 
            self.cvar.notify_all(); 
        }
    }

    /// Tries popping txs from any of the queues. 
    /// 
    /// Checks ready queue 1st, and if no elements available, checks partial ready.
    /// Waits until signaled by another thread pushing a new element, or until no more txs
    /// to execute.
    fn pop(&self) -> Option<TxId> {

        #[cfg(feature = "debug")]
        {
            print_with_thread_id!("Ready queue: {:?}", *self.ready_queue.lock());
            print_with_thread_id!("Partial_Ready queue: {:?}", *self.partial_ready_queue.lock());
        }
        
        'try_popping: loop {

            // try fetching some tx from ready
            let ready_tx = if let Some(ready) = self.ready_queue.iter().next() {
                Some(*ready)
            } else { None };

            if let Some(ready) = ready_tx {
                self.ready_queue.remove(&ready);
                // self.set_tx_status(ready, TxState::Executing);
                return Some(ready);
            }

            // try fetching some tx from partial_ready
            let partial_ready_tx = if let Some(partial_ready) = self.partial_ready_queue.iter().next() {
                Some(*partial_ready)
            } else { None };

            if let Some(partial_ready) = partial_ready_tx {
                self.partial_ready_queue.remove(&partial_ready);
                // self.set_tx_status(partial_ready, TxState::Executing);
                return Some(partial_ready);
            }


            let mut lock = self.executed_txs.lock();
            while *lock < self.total_txs {
                self.cvar.wait(&mut lock);
                continue 'try_popping;
            }
            // has no message to execute
            break 'try_popping;
        }

        return None;
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum TxState {
    Executing,
    Executed,
    NotExecuted,
}

static ATOMIC_ORDERING: Ordering = Ordering::SeqCst;

#[derive(Debug)]
struct TransactionDependencies {
    dependencies: HashSet<TxId>,
    dependencies_counter: AtomicUsize,
}

impl TransactionDependencies {
    fn new() -> Self {
        TransactionDependencies {
            dependencies: HashSet::new(),
            dependencies_counter: AtomicUsize::new(0), 
        }
    }

    fn set_dependencies(&mut self, dependencies: HashSet<TxId>) {
        self.dependencies_counter.store(dependencies.len(), ATOMIC_ORDERING);
        self.dependencies = dependencies;
    }

    /// Checks if tx is a dependency.
    /// If yes, then decrements the dependency counter, returning true if it reached 0. 
    /// Returns false otherwise
    fn remove_dependency(&self, tx_id: TxId) -> bool {
        if self.dependencies.get(&tx_id).is_some() {
            let prev_val = self.dependencies_counter.fetch_sub(1, ATOMIC_ORDERING);
            return prev_val == 1;
        }
        
        return false
        
    } 
}

#[derive(Debug)]
pub struct ConcurrentSchedule {
    /// Stores state of each tx - Executing, Executed, NotExecuted - This is used when finishing tx execution.
    /// We update the dependencies of all txs that depend on the one we finished executing & then we use the tx status
    /// to filter when to push a tx that has no dependencies & hasn't started executing yet
    tx_states: Vec<TxState>,

    /// Total number of txs in the block
    total: TxId,

    /// Stores the id of txs that are the dependencies of some TxId
    /// txId -> txs which it depends on
    deps: Vec<Option<TransactionDependencies>>,

    /// stores the txs that depend on some tx
    /// Tx -> Set of txs depending on it
    dependent_txs: Vec<Option<HashSet<TxId>>>,

    /// stores the txs that have their 1st operation depending on it
    /// Tx -> Set of txs which their 1st operation depends on this tx
    partial_ready_tx: Vec<Option<HashSet<TxId>>>,

    /// Signal used when any tx is pushed either to READY or PARTIAL_READY queue
    pub execution_queues: ConcurrentQueues,

    /// mapping of SC_address -> key -> linked list of operations
    schedule: Schedule,

    #[cfg(feature="exec_time")]
    node_dependency_timer: Option<Instant>,
    #[cfg(feature="exec_time")]
    node_dependency_time: Duration,
    #[cfg(feature="exec_time")]
    node_creation_timer: Option<Instant>,
    #[cfg(feature="exec_time")]
    node_creation_time: Duration,

    timer_get: ConcurrentTimer,
    timer_set: ConcurrentTimer,
    timer_merge_comm_chain: ConcurrentTimer,
    timer_wait_for_msgs_from_queue: ConcurrentTimer,
    timer_update_execution_queues_on_tx_finish: ConcurrentTimer,
}

/// Iterator that allows iterating over each schdule/contract address
impl<'a> IntoIterator for &'a ConcurrentSchedule {
    type Item = dashmap::mapref::multiple::RefMulti<'a, ScAddr, SCSchedule>;
    type IntoIter = ConcurrentScheduleIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        ConcurrentScheduleIter {
            iter: self.schedule.schedule.iter(),
        }
    }
}

pub struct ConcurrentScheduleIter<'a> {
    iter: dashmap::iter::Iter<'a, ScAddr, SCSchedule>,
}

impl<'a> Iterator for ConcurrentScheduleIter<'a> {
    type Item = dashmap::mapref::multiple::RefMulti<'a, ScAddr, SCSchedule>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl PartialEq for ConcurrentSchedule {
    fn eq(&self, other: &ConcurrentSchedule) -> bool {
        self.tx_states == other.tx_states &&
        self.total == other.total &&
        self.compare_deps(other) &&
        self.compare_dependent_txs(other) &&
        self.compare_partial_ready_tx(other) &&
        self.execution_queues == other.execution_queues &&
        self.schedule == other.schedule
    }
}

impl ConcurrentSchedule {
    fn compare_deps(&self, other: &ConcurrentSchedule) -> bool {
        if self.deps.len() != other.deps.len() { return false; }
        
        // self.deps.iter().all(|ref_multi| {
        //     let (key, set1) = ref_multi.pair();
        //     match other.deps.get(key) {
        //         Some(set2) => {
        //             set1.len() == set2.len() && 
        //             set1.iter().all(|item| set2.contains(item.key()))
        //         },
        //         None => false,
        //     }
        // })
        todo!()
    }

    fn compare_dependent_txs(&self, other: &ConcurrentSchedule) -> bool {
        if self.dependent_txs.len() != other.dependent_txs.len() { return false; }
        
        // self.dependent_txs.iter().all(|ref_multi| {
        //     let (key, set1) = ref_multi.pair();
        //     match other.dependent_txs.get(key) {
        //         Some(set2) => {
        //             set1.len() == set2.len() && 
        //             set1.iter().all(|item| set2.contains(item))
        //         },
        //         None => false,
        //     }
        // })
        todo!()
    }

    fn compare_partial_ready_tx(&self, other: &ConcurrentSchedule) -> bool {
        if self.partial_ready_tx.len() != other.partial_ready_tx.len() { return false; }
        
        // self.partial_ready_tx.iter().all(|ref_multi| {
        //     let (key, set1) = ref_multi.pair();
        //     match other.partial_ready_tx.get(key) {
        //         Some(set2) => {
        //             set1.len() == set2.len() && 
        //             set1.iter().all(|item| set2.contains(item))
        //         },
        //         None => false,
        //     }
        // })
        todo!()
    }
}

impl ConcurrentSchedule {
    pub fn new() -> Self {
        ConcurrentSchedule {
            tx_states: vec![],
            total: 0,

            deps: Vec::new(),

            execution_queues: ConcurrentQueues::new(),
            
            schedule: Schedule::new(),
            
            dependent_txs: Vec::new(),

            partial_ready_tx: Vec::new(),

            #[cfg(feature = "exec_time")]
            node_dependency_timer: None,
            #[cfg(feature = "exec_time")]
            node_dependency_time: Duration::ZERO,
            #[cfg(feature = "exec_time")]
            node_creation_timer: None,
            #[cfg(feature = "exec_time")]
            node_creation_time: Duration::ZERO,

            timer_get: ConcurrentTimer::new(),
            timer_set: ConcurrentTimer::new(),
            timer_merge_comm_chain: ConcurrentTimer::new(),
            timer_wait_for_msgs_from_queue: ConcurrentTimer::new(),
            timer_update_execution_queues_on_tx_finish: ConcurrentTimer::new(),
        }
    }

    pub fn from_schedule_builder(mut schedule: ScheduleBuilder) -> ConcurrentSchedule {
            
        let mut deps_hash_sets = Vec::with_capacity(schedule.total);
        for _ in 0..schedule.total {
            deps_hash_sets.push(Some(TransactionDependencies::new()))
        }
        for i in 0..schedule.deps.len() {
            if let Some(dep) = schedule.deps[i].take() {
                deps_hash_sets[i].as_mut().unwrap().set_dependencies(dep);
            }
        }

        let execution_queues = ConcurrentQueues::from_serial_queues(schedule.execution_queues);

        ConcurrentSchedule {
            tx_states: schedule.tx_states,
            total: schedule.total,

            deps: deps_hash_sets,

            execution_queues,
            
            schedule: schedule.schedule,
            
            dependent_txs: schedule.dependent_txs,

            partial_ready_tx: schedule.partial_ready_tx,

            #[cfg(feature = "exec_time")]
            node_dependency_timer: None,
            #[cfg(feature = "exec_time")]
            node_dependency_time: Duration::ZERO,
            #[cfg(feature = "exec_time")]
            node_creation_timer: None,
            #[cfg(feature = "exec_time")]
            node_creation_time: Duration::ZERO,

            timer_get: ConcurrentTimer::new(),
            timer_set: ConcurrentTimer::new(),
            timer_merge_comm_chain: ConcurrentTimer::new(),
            timer_wait_for_msgs_from_queue: ConcurrentTimer::new(),
            timer_update_execution_queues_on_tx_finish: ConcurrentTimer::new(),
        }
    }

    #[cfg(feature = "exec_time")]
    fn start_node_dependency_timer(&mut self) {
        self.node_dependency_timer = Some(Instant::now());
    }

    #[cfg(feature = "exec_time")]
    fn stop_node_dependency_timer(&mut self) {
        let elapsed = self.node_dependency_timer.unwrap().elapsed();
        self.node_dependency_time += elapsed;
    }

    #[cfg(feature = "exec_time")]
    fn start_node_creation_timer(&mut self) {
        self.node_creation_timer = Some(Instant::now());
    }

    #[cfg(feature = "exec_time")]
    fn stop_node_creation_timer(&mut self) {
        let elapsed = self.node_creation_timer.unwrap().elapsed();
        self.node_creation_time += elapsed;
    }

    /// Updates the execution state of a transaction.
    /// This is done without any locking mechanisms as txs are already synchronized
    /// via the READY and PARTIAL_READY queues.
    fn set_tx_status(&self, tx_id: TxId, tx_status: TxState) {
        if tx_id >= self.total { panic!("Tx id must be less than the total number of transactions") };
        let ptr = self.tx_states.as_ptr() as *mut TxState;
        unsafe { *ptr.offset(tx_id as isize) = tx_status }
    }

    /// Should be called when a tx/message is finished executing
    /// Runs over the dependencies on the tx_id (current tx that finished executing),
    /// and decreases the dependency count on each by 1.
    /// If any of those reaches dependency count of 0 & is not executing => push to READY_QUEUE.
    /// At the end, push all partial_ready into PARTIAL_READY_QUEUE
    /// If is an instantiation, also mark the instantiation dependency as complete.
    pub fn on_tx_finish(&self, tx_id: TxId) {
        #[cfg(feature = "exec_time")]
        let timer = self.timer_update_execution_queues_on_tx_finish.create_scoped_timer();

        let mut ready_txs = vec![];
        let mut partial_ready_txs = vec![];

        let mut txs_to_be_excluded_from_partial_ready = HashSet::new();

        // if tx has other txs depending on it - decrease the dependency count & partial_ready count as well
        if let Some(dependent_txs) = &self.dependent_txs[tx_id] {
            for dependent_tx in dependent_txs.iter() {
                let dependencies = self.deps[*dependent_tx].as_ref().unwrap();
                let no_dependencies_left = dependencies.remove_dependency(tx_id);
    
                let tx_status = self.tx_states[*dependent_tx];
                if no_dependencies_left && (tx_status == TxState::NotExecuted) {

                    ready_txs.push(*dependent_tx);
                    txs_to_be_excluded_from_partial_ready.insert(dependent_tx);
                }
            }
        }

        // if tx has tx_partials - push them to partial ready queue
        if let Some(current_tx_partials) = &self.partial_ready_tx[tx_id] {
            for tx in current_tx_partials.iter() {
                if !txs_to_be_excluded_from_partial_ready.contains(tx) {
                    partial_ready_txs.push(*tx);
                }
            }
        }

      
        self.set_tx_status(tx_id, TxState::Executed);

        self.execution_queues.push_and_signal(ready_txs, partial_ready_txs);

        #[cfg(feature = "exec_time")]
        self.timer_update_execution_queues_on_tx_finish.add_scoped_timer(timer);

    }

    pub fn get_next_message_to_execute(&self) -> Option<TxId> {
        #[cfg(feature= "exec_time")]
        let timer = self.timer_wait_for_msgs_from_queue.create_scoped_timer();

        let tx = self.execution_queues.pop();
        
        #[cfg(feature= "exec_time")]
        self.timer_wait_for_msgs_from_queue.add_scoped_timer(timer);

        tx
    }

    /// Given a state manager (a struct that keeps info about the state of each SC),
    /// It runs over all SC addresses & keys stored in the schedules, fetches the last non commutative write
    /// node of each & saves the value of that node to storage
    pub fn persist_schedule<A, S, W, Q, E>(&self, state_manager: &SCManager<A, S, W, Q, E>) 
    where
        A: BackendApi,
        S: ConcurrentStorage,
        W: StorageWrapper,
        Q: Querier,
        E: ProfileGenerator
    {
        // run over each schedule of each SC
        for schedule in &*self {
            let sc_address = schedule.key();
            let sc_storage = state_manager.get_contract_storage(sc_address.clone());
            // run over all keys of each SC
            for operations_per_key in schedule.value() {
                let key = operations_per_key.key();
                let LastWrites { commutative, non_commutative } = self.schedule.get_last_writes(&sc_address, key);

                // persist last write - If it is commutative, then merge the deltas
                match (commutative, non_commutative) {
                    // TODO - refactor this to use the method from LastWrites
                    (Some(comm), Some(non_comm)) => {
                        let comm_id = comm.read().data.tx_block_id;
                        let non_comm_id = non_comm.read().data.tx_block_id;

                        if comm_id > non_comm_id { 
                            let node_val = self.merge_commutative_chain(&comm, &sc_storage, key);
                            sc_storage.set(key, node_val.as_slice()).0.unwrap();
                        }
                        else {
                            let node_val = &non_comm.read().data.value;
                            let node_val = node_val.wait_for_value();
                            sc_storage.set(key, node_val.as_slice()).0.unwrap();
                        }
                    },
                    
                    (Some(comm), None) => {
                        let node_val = self.merge_commutative_chain(&comm, &sc_storage, key);
                        sc_storage.set(key, node_val.as_slice()).0.unwrap();
                    },

                    (None, Some(non_comm)) => {
                        let node_val = &non_comm.read().data.value;
                        let node_val = node_val.wait_for_value();
                        sc_storage.set(key, node_val.as_slice()).0.unwrap();
                    },
                    (None, None) => ()
                }
            }
        }
    }

    /// Searches for the previous commutative read associated to the passed commutative write node
    fn get_prev_incr_read(node: &NodeRef<VecOperation>) -> NodeRef<VecOperation> {
        let node_read_lock = node.read();
        let tx_id = node_read_lock.data.tx_block_id;
        let mut previous_op = Arc::clone(node_read_lock.prev.as_ref().unwrap());

        return loop {
            let node_lock = previous_op.read();

            // If we found the Commutative read -> return it
            if node_lock.data.is_commutative() && 
               node_lock.data.is_read()  && 
               node_lock.data.tx_block_id == tx_id {
                break Arc::clone(&previous_op);
            };

            // Else keep looking
            if let Some(dependency)  = &node_lock.prev {
                let tmp = Arc::clone(dependency);
                drop(node_lock); // since node_lock borrows from previous_op. Needed for below assignment 

                previous_op = tmp;
            } 
            else {
                panic!("No Commutative Read was found in the schedule before the commutative write corresponding to this node: {:?}", node);
            }
        }
    }

    /// Given a node and a value, set the corresponding value on the node.
    /// This value can either be the passed value, or a value that depends on the passed
    /// value.
    /// 
    /// If the node is Commutative, then the actual value set for the node is a Delta, computed
    /// using both the preceding Commutative Read and the passed value to this function.
    pub fn set_value(&self, node: &NodeRef<VecOperation>, value: &[u8]) {
        
        #[cfg(feature = "exec_time")]
        let timer = self.timer_set.create_scoped_timer();

        // fetch node info
        let node_read_lock = node.read();
        let op_type = node_read_lock.data.operation_type;
        let commutativity = node_read_lock.data.commutativity;
        drop(node_read_lock);

        match op_type {
            OpType::Read => {
                match commutativity {
                    Commutativity::Commutative => {
                        let node = node.read();
                        node.data.set_value(value.to_vec());
                    },
                    Commutativity::NonCommutative => {} // no need to write the read value to the node
                }
            },
             OpType::Write => {
                match commutativity {
                    Commutativity::Commutative => {

                        #[cfg(feature = "debug")]
                        print_with_thread_id!("Setting commutative val");
                        
                        let prev_incr_read = ConcurrentSchedule::get_prev_incr_read(node);

                        let read_lock = prev_incr_read.read();
                        let prev_incr_read_val = read_lock.data.value.get_value().unwrap();
                        
                        #[cfg(feature = "debug")]
                        print_with_thread_id!("Prev incr read {:?}", prev_incr_read_val);

                        let val = value.to_vec();
                        let delta = val.compute_delta(&prev_incr_read_val);
                        drop(read_lock);

                        #[cfg(feature = "debug")]
                        print_with_thread_id!("Writing to commutative node");
                        let node_write_lock = node.read();
                        node_write_lock.data.set_value(delta);

                        #[cfg(feature = "debug")]
                        print_with_thread_id!("Finished setting commutative value");

                    },
                    Commutativity::NonCommutative => {
                        let node = node.read();
                        node.data.set_value(value.to_vec());
                    }
                }
             }
        };

        #[cfg(feature = "exec_time")]
        self.timer_set.add_scoped_timer(timer);
    }

    /// Given a node, start running over the linked list (previous nodes) & merge all the 
    /// deltas until reaching this node. If we reach the head of the list, then no NonComm Write
    /// was found -> fetch the initial value from storage.
    /// 
    /// In the example below, 'node' parameter refers to the first Commutative dependency of a Non commutative
    /// operation. Meaning if we want to know the read value by NonComm_Read operation, then we need to pass
    /// the 'Comm_2' node to this function, aka the NonComm_Read's dependency.
    /// 
    /// ```markdown
    /// (NonComm_Write) <- (Comm_write_1) <- (Comm_write_2) <- (NonComm_Read)
    /// ```
    fn merge_commutative_chain<S>(&self, node: &NodeRef<VecOperation>, storage: &Arc<S>, key: &[u8]) -> Vec<u8> 
    where
        S: ConcurrentStorage + ?Sized // allows handling both 'S: ConcurrentStorage' and 'dyn ConcurrentStorage'
    {
        #[cfg(feature = "exec_time")]
        let timer = self.timer_merge_comm_chain.create_scoped_timer();

        let mut starting_node = Arc::clone(node);
        let mut accumulated_deltas =  vec![];

        // auxilliary function
        let mut merge_accumulated_delta = |delta: &Vec<u8>| {
            if accumulated_deltas.is_empty() {
                accumulated_deltas = delta.clone();
            }
            else {
                accumulated_deltas.merge(delta);
            }
        };

        #[cfg(feature = "debug")]
        print_with_thread_id!("Mergind deltas");

        let res = loop {
            let node_lock = starting_node.read();
            // Commutative writes -> merge deltas
            if node_lock.data.is_write() {

                #[cfg(feature = "debug")]
                print_with_thread_id!("Waiting for value on write of tx {:?}", node_lock.data.tx_block_id);
                
                let value = node_lock.data.wait_for_value();
                
                #[cfg(feature = "debug")]
                print_with_thread_id!("Finished waiting on write of tx {:?}", node_lock.data.tx_block_id);

                merge_accumulated_delta(value);

                // This is a sufficient condition to stop. The first NonCommutative Write (of any tx tx) after a chain of 
                // commutative operations will always be the 'barrier' of all subsequent commutative operations.
                // They will always depend on this write.
                if !node_lock.data.is_commutative() {
                    break accumulated_deltas;
                }
            }

            // Current node has a previous node
            if let Some(prev)  = &node_lock.prev {
                let tmp = Arc::clone(prev);

                drop(node_lock); // since node_lock borrows from previous_op. Needed for below assignment 
                starting_node = tmp;
            } 
            else { // We reached the head without finding any non commutative write -> merge deltas to storage value
                let val = storage.get_uncharged(key).unwrap();
                merge_accumulated_delta(&val);
                break accumulated_deltas;
 
            }
        };

        #[cfg(feature = "exec_time")]
        let timer = self.timer_merge_comm_chain.add_scoped_timer(timer);

        res
    }


    /// Given a read node, returns the value it is supposed to read from if any.
    /// If the node is a Commutative Read && has a dependency on a previous write:
    /// 
    /// - Then that write can only be Non commutative, as commutative operations do not conflict.
    /// Then, wait for the write to complete & read its value.
    /// 
    /// If the node is Non commutative Read & has dependency on a previous write:
    /// 
    /// - If write is commutative - run back through the chain of all commutative operations
    /// summing the deltas to the firs non commutative write found.
    /// 
    /// - If the write is non commutative - just wait for it.
    /// 
    /// 
    /// If the node has no dependency, then cannot read any value from schedule.
    /// It must be read from storage.
    pub fn get_value(&self, read_node: &NodeRef<VecOperation>, concurrent_storage: &Arc<dyn ConcurrentStorage>, 
        sc_address: &ScAddr, key: &[u8]) -> Option<Vec<u8>> {

        #[cfg(feature = "exec_time")]
        let timer = self.timer_get.create_scoped_timer();

        // fetch node info
        let node_read_lock = read_node.read();

        let val = if node_read_lock.data.is_read() {
            if node_read_lock.data.is_commutative() {

                let dependency_val = if let Some(dependency) = &node_read_lock.dependency {
                    let node_lock = dependency.read();
                    // println!("Comm Read depnded on: {:?}", node_lock.data);
                    Some(node_lock.data.wait_for_value().clone())
                }
                else {
                    concurrent_storage.get_uncharged(key)
                };

                let val: Vec<u8> = dependency_val.as_ref().unwrap().clone();

                node_read_lock.data.set_value(val);
                dependency_val
            }
            else {
                if let Some(dependency) = &node_read_lock.dependency {
                    let node_lock = dependency.read(); 

                    if node_lock.data.is_commutative() {

                        #[cfg(feature = "debug")]
                        print_with_thread_id!("Getting a non commutative value depending on a commutative node");
                        
                        drop(node_lock);
                        let merged_deltas = self.merge_commutative_chain(dependency, concurrent_storage, key);
                        
                        #[cfg(feature = "debug")]
                        print_with_thread_id!("Finished getting the dependent value");

                        Some(merged_deltas)
                    }
                    else {
                        Some(node_lock.data.wait_for_value().clone())
                    }
                }
                else {
                    concurrent_storage.get_uncharged(key)
                }
            }
        }
        else {
            panic!("This method should only be called for read nodes!")
        };

        #[cfg(feature = "exec_time")]
        self.timer_get.add_scoped_timer(timer);

        val
    }



    pub fn print_times(&self, n_threads: u16) {
        println!("CONCURRENT_SCHEDULE ---");
        println!("timer_get: ~{:?} per thread", self.timer_get.get_value() / (n_threads as u32));
        println!("timer_set: ~{:?} per thread", self.timer_set.get_value() / (n_threads as u32));
        println!("timer_merge_comm_chain: ~{:?} per thread", self.timer_merge_comm_chain.get_value() / (n_threads as u32));
        println!("timer_wait_for_msgs_from_queue: ~{:?} per thread", self.timer_wait_for_msgs_from_queue.get_value() / (n_threads as u32));
        println!("timer_update_execution_queues_on_tx_finish: ~{:?} per thread", self.timer_update_execution_queues_on_tx_finish.get_value() / (n_threads as u32));
        println!("---");
    }

    #[cfg(feature = "debug_graph")]
    pub fn generate_debug_graph(&self, graph_name: String, rws:  &Arc<Vec<RWSContext>>) {
        let mut dot = DotSchedule::new(NodeColor::LightBlue, 2);

        let dot_file = dot.parse(self, &rws);
        dot.save_as_png(dot_file, graph_name).unwrap();
    }

}


#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use serial_test::serial;
    use wasmer::Store;

    use crate::{
        internals::instance_from_module, symb_exec::{Commutativity, ReadWrite}, testing::{
            mock_concurrent_backend, mock_persistent_backend, mock_tx_operation, 
            ConcurrentStorage, MockApi, MockConcurrentStorage, MockQuerier, MockStorageWrapper
        }, vm_manager::{
            schedule::{OperationValue, ScAddr}, serial_schedule::ScheduleBuilder,
        }, wasm_backend::{compile, make_compiling_engine}, ConcurrentSchedule, InstanceOptions, SCManager, Size, SymbolicExecutionEngine
    };

    use super::{NodeRef, VecOperation};

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");
    const SC_ADDR_A: &str = &"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const HIGH_GAS_LIMIT: u64 = 20_000_000_000_000; // ~20s, allows many calls on one instance
    const DEFAULT_MEMORY_LIMIT: Size = Size::mebi(64);

    fn assert_node_next(node: &NodeRef<VecOperation>, node_next: &NodeRef<VecOperation>) {
        let node = node.read();
        let next = node.next.as_ref().unwrap().read();

        let node_next = node_next.read();

        assert_eq!(*next, *node_next);
    }

    fn assert_node_prev(node: &NodeRef<VecOperation>, node_prev: &NodeRef<VecOperation>) {
        let node = node.read();
        let next = node.prev.as_ref().unwrap().read();

        let node_prev = node_prev.read();

        assert_eq!(*next, *node_prev);
    }

    fn assert_node_dependency(node: &NodeRef<VecOperation>, node_dep: &NodeRef<VecOperation>) {
        let node = node.read();
        let next = node.dependency.as_ref().unwrap().read();

        let node_dep = node_dep.read();

        assert_eq!(*next, *node_dep);
    }

    fn mock_state_manager(sc_address: ScAddr) -> SCManager<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier, SymbolicExecutionEngine> {
        // create a state manager
        let state_manager: SCManager<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier, SymbolicExecutionEngine> = SCManager::new(Arc::new(SymbolicExecutionEngine::new()));
        state_manager.save_code(CONTRACT, None).unwrap();

        assert_eq!(state_manager.get_code(0).unwrap(), CONTRACT);
        
        // Create the compiled module & storage
        let code = state_manager.get_code(0).unwrap();
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        let module: wasmer::Module = compile( &engine, code.as_slice()).unwrap();
        let concurrent_store = Arc::new(MockConcurrentStorage::default());
        let backend = Arc::new(mock_persistent_backend(&[], Arc::clone(&concurrent_store)));

        let store = Store::new(engine);
        let much_gas: InstanceOptions = InstanceOptions { gas_limit: HIGH_GAS_LIMIT };
        let concurrent_backend = mock_concurrent_backend(&[], concurrent_store);
        let instance = instance_from_module(store, &module, concurrent_backend, much_gas.gas_limit, None).unwrap();
        let instances = vec![instance];


        state_manager.save_instances(0, sc_address, backend, instances);
        
        state_manager
    }

    // Storage | <- [Non Comm Read]
    #[test]
    #[serial]
    fn get_value_non_commutative_depends_on_storage() {
        let key = vec![0u8];
        let val = "100".as_bytes().to_vec();

        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 0, ReadWrite::read(), Commutativity::NonCommutative),

        ];

        let mut builder = ScheduleBuilder::new();
        builder.build_from_rws(&mut rws);

        let concurrent_schedule = ConcurrentSchedule::from_schedule_builder(builder);

        let operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let node = match operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());
        concurrent_storage.set(key.as_slice(), val.as_slice()).0.unwrap(); 


        let read_val = concurrent_schedule.get_value(node, &concurrent_storage, &SC_ADDR_A.to_owned(), &key);

        assert_eq!(read_val, Some(val));
        // Read
        assert_eq!(node.read().data.value, OperationValue::new());
    }

    // Storage | <- [Comm Read]
    // Should update the value read in the node
    #[test]
    #[serial]
    fn get_value_commutative_depends_on_storage() {
        let key = vec![0u8];
        let val = "100".as_bytes().to_vec();

        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 0, ReadWrite::read(), Commutativity::Commutative),

        ];

        let mut builder = ScheduleBuilder::new();
        builder.build_from_rws(&mut rws);

        let concurrent_schedule = ConcurrentSchedule::from_schedule_builder(builder);
        let operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let node = match operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());
        concurrent_storage.set(key.as_slice(), val.as_slice()).0.unwrap(); 


        let read_val = concurrent_schedule.get_value(node, &concurrent_storage, &SC_ADDR_A.to_owned(), &key);

        assert_eq!(read_val, Some(val.clone()));
        assert_eq!(node.read().data.value.get_value(), Some(&val));
    }

    // Storage | <- [Comm Read] <- [Comm Write]
    // Should update the value read in the node
    #[test]
    #[serial]
    fn set_value_commutative_depends_on_commutative_read() {
        let key = vec![0u8];
        let val = "100".as_bytes().to_vec();

        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 0, ReadWrite::read(),  Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 0, ReadWrite::write(), Commutativity::Commutative),

        ];

        let mut builder = ScheduleBuilder::new();
        builder.build_from_rws(&mut rws);

        let concurrent_schedule = ConcurrentSchedule::from_schedule_builder(builder);
                
        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());
        concurrent_storage.set(key.as_slice(), val.as_slice()).0.unwrap();

        // read node
        let operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let node = match operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        concurrent_schedule.get_value(node, &concurrent_storage, &SC_ADDR_A.to_owned(), &key);

        // write node
        let operation = rws.get(1).unwrap().rws.rws.get(0).unwrap();
        let node = match operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
 
        concurrent_schedule.set_value(node, "105".as_bytes());

        // write commutative node should end up having the delta -> 105 - 100 = 5
        assert_eq!(node.read().data.value.get_value(), Some(&"5".as_bytes().to_vec()));
    }

    // Storage | [Non Comm Write] <- [Non Comm Read]
    #[test]
    #[serial]
    fn get_value_non_commutative_depends_on_non_commutative_write() {
        let key = vec![0u8];
        let val = "100".as_bytes().to_vec();

        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 0, ReadWrite::write(), Commutativity::NonCommutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 1, ReadWrite::read(),  Commutativity::NonCommutative),
        ];

        let mut builder = ScheduleBuilder::new();
        builder.build_from_rws(&mut rws);

        let concurrent_schedule = ConcurrentSchedule::from_schedule_builder(builder);

        let write_operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };

        concurrent_schedule.set_value(write_node, &val);

        let read_operation = rws.get(1).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());

        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A.to_owned(), &key);

        assert_eq!(read_val, Some(val));
    }

    // Storage | <- [Comm Read] <- [Comm write] <- [Non Comm Read]
    #[test]
    #[serial]
    fn get_value_non_commutative_depends_on_commutative_write_depending_on_storage() {
        let key = vec![0u8];
        let val = "100".as_bytes().to_vec();
        let comm_write = "109".as_bytes().to_vec();
        let delta = "9".as_bytes().to_vec();
        let final_val = "109".as_bytes().to_vec();

        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 0, ReadWrite::read(), Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 0, ReadWrite::write(), Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 1, ReadWrite::read(),  Commutativity::NonCommutative),
        ];

        let mut builder = ScheduleBuilder::new();
        builder.build_from_rws(&mut rws);

        let concurrent_schedule = ConcurrentSchedule::from_schedule_builder(builder);

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());
        concurrent_storage.set(key.as_slice(), val.as_slice()).0.unwrap();

        // Comm read -> read X
        let read_operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A.to_owned(), &key);
        assert_eq!(read_val, Some(val));

        // Comm write -> write Z = Y - X
        let write_operation = rws.get(1).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        concurrent_schedule.set_value(write_node, &comm_write);
        assert_eq!(write_node.read().data.value.get_value(), Some(&delta));

        // NonComm read -> read X + Z = Y
        let read_operation = rws.get(2).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A.to_owned(), &key);

        assert_eq!(read_val, Some(final_val));
    }


    // Storage | <- [Non Comm Write] <- [Comm Read] <- [Comm write] <- [Non Comm Read]
    #[test]
    #[serial]
    fn get_value_non_commutative_depends_on_commutative_write_depending_on_non_comm_write() {
        let key = vec![0u8];
        let val = "100".as_bytes().to_vec();
        let comm_write = "109".as_bytes().to_vec();
        let delta = "9".as_bytes().to_vec();
        let final_val = "109".as_bytes().to_vec();

        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 0, ReadWrite::write(), Commutativity::NonCommutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 1, ReadWrite::read(),  Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 1, ReadWrite::write(), Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 2, ReadWrite::read(),  Commutativity::NonCommutative),
        ];

        let mut builder = ScheduleBuilder::new();
        builder.build_from_rws(&mut rws);

        let concurrent_schedule = ConcurrentSchedule::from_schedule_builder(builder);

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());

        // NonComm write -> write X
        let write_operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        concurrent_schedule.set_value(write_node, val.as_slice());
        assert_eq!(write_node.read().data.value.get_value(), Some(&val.clone()));

        // Comm read -> read X
        let read_operation = rws.get(1).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A.to_owned(), &key);
        assert_eq!(read_val, Some(val));

        // Comm write -> write Z = Y - X
        let write_operation = rws.get(2).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        concurrent_schedule.set_value(write_node, &comm_write);
        assert_eq!(write_node.read().data.value.get_value(), Some(&delta));

        // NonComm read -> read X + Z = Y
        let read_operation = rws.get(3).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A.to_owned(), &key);

        assert_eq!(read_val, Some(final_val));
    }


    // Storage | <- [Comm Read] <- [Comm write] <- [Comm Read] <- [Comm write] <- [Non Comm Read]
    // last non commutative read should see the sum of the previous two deltas over the value in storage
    #[test]
    #[serial]
    fn get_value_non_commutative_depends_on_two_commutative_operations() {
        let key = vec![0u8];
        let val = "100".as_bytes().to_vec();
        let comm_write1 = "109".as_bytes().to_vec();
        let delta1 = "9".as_bytes().to_vec();
        let comm_write2 = "104".as_bytes().to_vec();
        let delta2 = "4".as_bytes().to_vec();
        let final_val = "113".as_bytes().to_vec();

        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 0, ReadWrite::read(),  Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 0, ReadWrite::write(), Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 1, ReadWrite::read(),  Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 1, ReadWrite::write(), Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &key, 2, ReadWrite::read(),  Commutativity::NonCommutative),
        ];

        let mut builder = ScheduleBuilder::new();
        builder.build_from_rws(&mut rws);

        let concurrent_schedule = ConcurrentSchedule::from_schedule_builder(builder);

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());
        concurrent_storage.set(key.as_slice(), val.as_slice()).0.unwrap();

        // Comm read1
        let read_operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A.to_owned(), &key);
        assert_eq!(read_val, Some(val.clone()));

        // Comm write1
        let write_operation = rws.get(1).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        concurrent_schedule.set_value(write_node, &comm_write1);
        assert_eq!(write_node.read().data.value.get_value(), Some(&delta1));

        // Comm read2
        let read_operation = rws.get(2).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A.to_owned(), &key);
        assert_eq!(read_val, Some(val));

        // Comm write2
        let write_operation = rws.get(3).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        concurrent_schedule.set_value(write_node, &comm_write2);
        assert_eq!(write_node.read().data.value.get_value(), Some(&delta2));

        // NonComm read
        let read_operation = rws.get(4).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A.to_owned(), &key);

        assert_eq!(read_val, Some(final_val));
    }

    #[test]
    #[serial]
    fn perfect_rws_persist_storage() {
        let write_key = vec![1u8];
        let val = vec![12u8];
        let sc_address = SC_ADDR_A.to_owned();

        let mut rws = vec![
            mock_tx_operation(sc_address.clone(), &write_key, 0, ReadWrite::write(), Commutativity::NonCommutative),
        ];

        // build schedule
        let mut builder = ScheduleBuilder::new();
        builder.build_from_rws(&mut rws);

        let concurrent_schedule = ConcurrentSchedule::from_schedule_builder(builder);

        // get write node
        let schedule = &concurrent_schedule.schedule.schedule;
        let sc_schedule = schedule.get(&sc_address).unwrap();
        let linked_list = sc_schedule.get(&write_key).unwrap();
        let write_operation = linked_list.head.read();

        // set write node's value
        concurrent_schedule.set_value(&*write_operation, val.as_slice());

        let state_manager = mock_state_manager(sc_address.clone());

        // persist write in the created state manager
        concurrent_schedule.persist_schedule(&state_manager);

        // check persistance
        let res = state_manager.get_contract_storage(sc_address).get(&write_key);
        let value = res.0.unwrap().unwrap();

        assert_eq!(value, val); 

    }

    #[test]
    #[serial]
    fn on_tx_finish_no_dependencies_no_partials() {
        // let sc_address = SC_ADDR_A.to_owned();
        // let key = vec![1u8];

        // let mut concurrent_schedule = ConcurrentSchedule::new();
        // concurrent_schedule.build_from_rws(&mut vec![
        //     mock_tx_operation(sc_address, &key, 0, ReadWrite::write(), Commutativity::NonCommutative),
        // ]);
        
        // // insert untracked write
        // let op_node_write = DependencyNode::new_ref(OpType::Write, 0, Commutativity::NonCommutative, true);
        // concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node_write));
        
        // concurrent_schedule.get_next_message_to_execute();
        // concurrent_schedule.on_tx_finish(0);

        // let deps = &concurrent_schedule.deps;
        // assert_eq!(deps[0 as usize].as_ref().unwrap().len(), 0);
        todo!()
    }

}