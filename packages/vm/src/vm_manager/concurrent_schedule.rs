use std::{
    collections::{HashMap, HashSet, VecDeque}, sync::{atomic::{AtomicUsize, Ordering}, mpsc, Arc}, thread, time::{Duration, Instant}
};

use rayon::prelude::*;

use parking_lot::{Mutex, Condvar, RwLock};

use dashmap::{DashMap, DashSet};

use crate::{print_with_thread_id, symb_exec::{Commutativity, Key, ReadWrite}, testing::{ConcurrentStorage, StorageWrapper}, vm_manager::schedule::MergeableValue, BackendApi, Querier, SCManager};

use super::{schedule::{DependencyNode, NodeRef, OpType, Operation, SCSchedule, ScAddr, TxId, VecOperation}, serial_schedule::{ScheduleBuilder, SerialQueues}, vm_manager::RWSContext, LastWrites, Schedule};

#[cfg(feature = "debug_graph")]
use super::dot_schedule::{DotSchedule, NodeColor};

#[derive(Debug)]
pub struct ConcurrentQueues {
    executed_txs: Mutex<TxId>,

    total_txs: TxId,

    ready_queue: Mutex<VecDeque<TxId>>,
    partial_ready_queue: Mutex<VecDeque<TxId>>,

    cvar: Condvar,
}

impl PartialEq for ConcurrentQueues {
    fn eq(&self, other: &Self) -> bool {
        *self.executed_txs.lock() ==  *other.executed_txs.lock() &&
        self.total_txs == other.total_txs &&
        *self.ready_queue.lock() == *other.ready_queue.lock() &&
        *self.partial_ready_queue.lock() == *other.partial_ready_queue.lock()
    }
}

impl ConcurrentQueues {
    fn new() -> ConcurrentQueues {
        ConcurrentQueues {
            executed_txs: Mutex::new(0),

            total_txs: 0,

            ready_queue: Mutex::new(VecDeque::new()),
            partial_ready_queue: Mutex::new(VecDeque::new()),
        
            cvar: Condvar::new(),
        }
    }

    fn from_serial_queues(serial_queues: SerialQueues) -> ConcurrentQueues {
        ConcurrentQueues {
            executed_txs: Mutex::new(serial_queues.executed_txs),
            total_txs: serial_queues.total_txs,
            ready_queue: Mutex::new(serial_queues.ready_queue),
            partial_ready_queue: Mutex::new(serial_queues.partial_ready_queue),
            cvar: Condvar::new(),
        }
    }

    /// Merges 2 concurrent queues assuming that the 'other' queue already has an updated
    /// ready & partial_ready queues accounting for the merged state of both schedules.
    /// 
    /// If schedule A has a TxA operation on key 1, then 'other' queue should not have
    /// any tx with an operation on key 1 placed in the ready_queue (this validation must be done outside this method)
    fn merge(&mut self, other: ConcurrentQueues) {
        self.total_txs = self.total_txs + other.total_txs;
        
        let ready = other.ready_queue.into_inner();
        let partial_ready = other.partial_ready_queue.into_inner();

        self.ready_queue.lock().extend(ready);
        self.partial_ready_queue.lock().extend(partial_ready);
    }

    /// Removes a txId from ready_queue
    fn remove_id_from_ready(&self, id: TxId) -> Option<TxId> {
        let mut ready = self.ready_queue.lock();

        if let Some(pos) = ready.iter().position(|&x| x == id) {
            ready.remove(pos)
        } else { None }
    }

    /// Removes a txId from partial_ready_queue
    fn remove_id_from_partial_ready(&self, id: TxId) {
        let mut partial_ready = self.partial_ready_queue.lock();

        if let Some(pos) = partial_ready.iter().position(|&x| x == id) {
            partial_ready.remove(pos);
        }
    }

    fn set_total_txs(&mut self, total_txs: TxId) {
        self.total_txs = total_txs;
    }

    /// Simple push to the ready queue. Does not signal waiting threads.
    /// Should only be called during schedule build
    fn push_ready(&self, ready: TxId) {
        self.ready_queue.lock().push_back(ready);
    }

    /// Removes an item from the queue by ID
    fn remove_partial_ready(&self, tx_id: TxId) {
        let mut idx = 0;
        let mut queue = self.partial_ready_queue.lock();
        for item in queue.iter() {
            if *item == tx_id { break; }
            idx += 1;
        }
        queue.remove(idx);
    }

    /// Simple push to the partial_ready queue. Does not signal waiting threads.
    /// Should only be called during schedule build
    fn push_partial_ready(&self, partial_ready: TxId) {
        self.partial_ready_queue.lock().push_back(partial_ready);
    }

    /// Pushes to both queues and signals waiting threads if needed.
    /// Should only be called after the tx has finished execution, as this method
    /// increases an internal counter that tracks the number of executed txs
    fn push_and_signal(&self, ready: Vec<TxId>, partial_ready: Vec<TxId>) {
        let total_txs = ready.len() + partial_ready.len();

        if ready.len() > 0 {
            let mut queue = self.ready_queue.lock();
            queue.extend(ready);
            drop(queue);
        }

        if partial_ready.len() > 0 {
            let mut queue = self.partial_ready_queue.lock();
            queue.extend(partial_ready);
            drop(queue);
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

            let mut ready_lock = self.ready_queue.lock();
            if let Some(ready) = ready_lock.pop_front() {
                return Some(ready);
            }
            drop(ready_lock);

            let mut partial_ready_lock = self.partial_ready_queue.lock();
            if let Some(partial_ready) = partial_ready_lock.pop_front() {
                return Some(partial_ready);
            }
            drop(partial_ready_lock);


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

#[derive(Debug)]
pub struct ConcurrentSchedule {
    /// Stores state of each tx - Executing, Executed, NotExecuted - This is used when finishing tx execution.
    /// We update the dependencies of all txs that depend on the one we finished executing & then we use the tx status
    /// to filter when to push a tx that has no dependencies & hasn't started executing yet
    tx_states: Vec<TxState>,

    // Set with an Id for each tx in the block
    transactions: HashSet<TxId>,

    /// Total number of txs in the block
    total: TxId,

    /// Stores the id of txs that are the dependencies of some TxId
    deps: Vec<Option<DashSet<TxId>>>,

    /// stores the txs that depend on some tx
    /// Tx -> Set of txs depending on it
    dependent_txs: DashMap<TxId, HashSet<TxId>>,

    /// stores the txs that have their 1st operation depending on it
    /// Tx -> Set of txs which their 1st operation depends on this tx
    partial_ready_tx: DashMap<TxId, HashSet<TxId>>,

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
        self.transactions == other.transactions &&
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
        true
    }

    fn compare_dependent_txs(&self, other: &ConcurrentSchedule) -> bool {
        if self.dependent_txs.len() != other.dependent_txs.len() { return false; }
        
        self.dependent_txs.iter().all(|ref_multi| {
            let (key, set1) = ref_multi.pair();
            match other.dependent_txs.get(key) {
                Some(set2) => {
                    set1.len() == set2.len() && 
                    set1.iter().all(|item| set2.contains(item))
                },
                None => false,
            }
        })
    }

    fn compare_partial_ready_tx(&self, other: &ConcurrentSchedule) -> bool {
        if self.partial_ready_tx.len() != other.partial_ready_tx.len() { return false; }
        
        self.partial_ready_tx.iter().all(|ref_multi| {
            let (key, set1) = ref_multi.pair();
            match other.partial_ready_tx.get(key) {
                Some(set2) => {
                    set1.len() == set2.len() && 
                    set1.iter().all(|item| set2.contains(item))
                },
                None => false,
            }
        })
    }
}

impl ConcurrentSchedule {
    pub fn new() -> Self {
        ConcurrentSchedule {
            tx_states: vec![],
            total: 0,

            transactions: HashSet::new(),

            deps: Vec::new(),

            execution_queues: ConcurrentQueues::new(),
            
            schedule: Schedule::new(),
            
            dependent_txs: DashMap::new(),

            partial_ready_tx: DashMap::new(),

            #[cfg(feature = "exec_time")]
            node_dependency_timer: None,
            #[cfg(feature = "exec_time")]
            node_dependency_time: Duration::ZERO,
            #[cfg(feature = "exec_time")]
            node_creation_timer: None,
            #[cfg(feature = "exec_time")]
            node_creation_time: Duration::ZERO,
        }
    }

    pub fn from_schedule_builder(mut schedule: ScheduleBuilder, n_threads: u16) -> ConcurrentSchedule {

        let mut keys: Vec<TxId> = schedule.deps.keys().cloned().collect();
        let mut total_keys = keys.len() as u16;

        
        // do not launch more threads than tx in the block
        let n_threads = if total_keys < n_threads { total_keys } 
        else { n_threads };
        let min_keys_per_thread = total_keys / n_threads;
        
        let deps_hash_sets: Arc<Vec<Option<DashSet<usize>>>> = Arc::new(vec![None; total_keys as usize]);


        let mut handles = vec![];
        for i in 0..n_threads {
            let deps_hash_sets_shared = Arc::clone(&deps_hash_sets);

            let keys_for_current_thread = if total_keys % (n_threads - i) != 0 { min_keys_per_thread + 1 }
            else { min_keys_per_thread };
            total_keys -= keys_for_current_thread;

            // extract txs from the block for current thread
            let key_subset: Vec<TxId> = keys.drain(0..(keys_for_current_thread as usize)).collect();
            
            let mut dependencies_to_push = Vec::with_capacity(key_subset.len());
            for k in &key_subset {
                dependencies_to_push.push(schedule.deps.remove(&k).unwrap());
            } 

            let handle = thread::spawn(move || {
                for k in key_subset {
                    let ptr = deps_hash_sets_shared.as_ptr() as *mut Option<DashSet<usize>>;
                    unsafe { *ptr.offset(k as isize) = Some(DashSet::from_iter(dependencies_to_push.remove(0).into_iter())) };
                }
            });

            handles.push(handle);
        }

        let execution_queues = ConcurrentQueues::from_serial_queues(schedule.execution_queues);
        let dependent_txs = DashMap::from_iter(schedule.dependent_txs.into_iter());
        let partial_ready_tx = DashMap::from_iter(schedule.partial_ready_tx.into_iter());

        for handle in handles {
            handle.join().unwrap();
        }

        let deps = Arc::into_inner(deps_hash_sets).unwrap();


        ConcurrentSchedule {
            tx_states: schedule.tx_states,
            total: schedule.total,

            transactions: schedule.transactions,

            deps: deps,

            execution_queues,
            
            schedule: schedule.schedule,
            
            dependent_txs,

            partial_ready_tx,

            #[cfg(feature = "exec_time")]
            node_dependency_timer: None,
            #[cfg(feature = "exec_time")]
            node_dependency_time: Duration::ZERO,
            #[cfg(feature = "exec_time")]
            node_creation_timer: None,
            #[cfg(feature = "exec_time")]
            node_creation_time: Duration::ZERO,
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
    pub fn on_tx_finish(&self, context: &RWSContext) {
        let tx_id = context.tx_block_id;

        let mut ready_txs = vec![];
        let mut partial_ready_txs = vec![];

        // if tx has dependent txs
        if let Some(dependent_txs) = self.dependent_txs.get(&tx_id) {
            for dependent_tx in dependent_txs.iter() {
                
                let dependencies = self.deps[*dependent_tx].as_ref().unwrap();
                dependencies.remove(&tx_id);
    
                let tx_status = self.tx_states[*dependent_tx];
                if dependencies.is_empty() && (tx_status == TxState::NotExecuted) {

                    ready_txs.push(*dependent_tx);
                    
                    let mut current_tx_partials = self.partial_ready_tx.get_mut(&tx_id).unwrap();
                    (*current_tx_partials).remove(dependent_tx);
                }
            }
        }

        // if tx has tx_partials - push them to partial ready queue
        if let Some(current_tx_partials) = self.partial_ready_tx.get(&tx_id) {
            for tx in current_tx_partials.iter() {
                partial_ready_txs.push(*tx);
            }
        }

      
        self.set_tx_status(tx_id, TxState::Executed);

        self.execution_queues.push_and_signal(ready_txs, partial_ready_txs);

    }

    pub fn get_next_message_to_execute(&self) -> Option<TxId> {
        self.execution_queues.pop()
    }

    /// Builds an execution schedule from a sequence of RWS's per messages.
    /// Run over each RWS & insert it in the schedule marking the dependencies between operations & transactions
    pub fn build_from_rws(&mut self, block: &mut Vec<RWSContext>) {

        self.total = block.len() as TxId;

        self.execution_queues.set_total_txs(self.total);
        self.tx_states = vec![TxState::NotExecuted ; self.total];
        // pre allocate initial space
        self.transactions = HashSet::with_capacity(self.total);
        self.dependent_txs = DashMap::with_capacity(self.total);
        
        self.deps = Vec::with_capacity(self.total);

        for i in 0..self.total {
            self.deps.push(Some(DashSet::new()));
        }


        for tx in block {

            let mut first_operation = true;
            let tx_id = tx.tx_block_id;
            let contract = tx.address;

            self.transactions.insert(tx_id);

            for operation in &mut tx.rws.rws {
                match operation {
                    ReadWrite::Read { 
                        storage_dependency: _, 
                        key, 
                        commutativity,
                        operation_node

                    } => {
                        let key_bytes = match key {
                            Key::Bytes(bytes) => bytes,
                            _ => unreachable!("Key should be bytes at this stage"),
                        };
                        // println!("Read COmmutativity: {:?}", commutativity);
                        *operation_node = Some(self.update_schedule_on_read_operation(first_operation, tx_id, contract, key_bytes, *commutativity));
                    }
                    ReadWrite::Write { 
                        storage_dependency: _, 
                        key, 
                        commutativity,
                        operation_node
                    } => {
                        let key_bytes = match key {
                            Key::Bytes(bytes) => bytes,
                            _ => unreachable!("Key should be bytes at this stage"),
                        };

                        *operation_node = Some(self.update_schedule_on_write_operation(first_operation, tx_id, contract, key_bytes, *commutativity));
                    }
                };

                if first_operation {
                    first_operation = false;
                }
            }

            if self.deps[tx_id].as_ref().unwrap().is_empty() { // no dependencies
                self.execution_queues.push_ready(tx_id);
                self.execution_queues.remove_partial_ready(tx_id);
            }
        }
    }

    /// Merge the state from 2 sequential partial schedules. The 'other' schedule is assumed to come after
    /// the 'self' schedule.
    /// 
    /// Set the dependencies of the first operations from the 'other' schedule as the last writes from the 
    /// 'self' schedule, update the 'prev' and 'next' fields of the nodes & update the ready & partial ready queues.
    // pub fn merge(&mut self, other: ConcurrentSchedule) {
    //     self.total = self.total + other.total;

    //     self.tx_states = vec![TxState::NotExecuted ; self.total];
    //     self.deps.extend(other.deps);
    //     self.dependent_txs.extend(other.dependent_txs);
    //     self.partial_ready_tx.extend(other.partial_ready_tx);
    //     self.transactions.extend(other.transactions);

    //     self.schedule.merge(other.schedule, &mut | node_self: NodeRef<VecOperation>, node_other: NodeRef<VecOperation>| {
    //         let node_other_tx_id = node_other.read().data.tx_block_id;
    //         let node_self_tx_id = node_self.read().data.tx_block_id; 
            
    //         self.deps[node_other_tx_id].insert(node_self_tx_id);
    //         self.dependent_txs.entry(node_self_tx_id).or_insert(HashSet::new()).insert(node_other_tx_id);
            
    //         let ready_tx = other.execution_queues.remove_id_from_ready(node_other_tx_id);

    //         // if is first operation of some tx from 'other' schedule, then remove it the 'other's from partial_ready_queue &
    //         // add it to the partial ready of the tx from the 'self' schedule  
    //         if node_other.read().data.first_operation {
    //             other.execution_queues.remove_id_from_partial_ready(node_other_tx_id);
    //             self.partial_ready_tx.entry(node_self_tx_id).or_insert(HashSet::new()).insert(node_other_tx_id);
    //         }
    //         // Was not first operation && was still in ready 
    //         // (meaning no other previous operation had a dependency) - inisert in partial_ready 
    //         else if let Some(tx) = ready_tx {
    //             self.execution_queues.push_partial_ready(tx);
    //         }
    //     });

    //     self.execution_queues.merge(other.execution_queues);

    // }

    pub fn insert_untracked_operation(&self, sc_address: ScAddr, key: &Vec<u8>, operation_node: NodeRef<VecOperation>) {
        let node_lock = operation_node.read();
        let op_type = node_lock.data.operation_type;
        let tx_id = node_lock.data.tx_block_id;
        let commutativity = node_lock.data.commutativity;
        drop(node_lock);

        if !self.transactions.contains(&tx_id) { 
            panic!(
                "Trying to insert a Read/Write operation from an unseen transaction!.
            Every transaction should have at least one Read/Write operation detected by the Symb Exec engine at the start."
            );
        }

        self.schedule.insert_untracked_operation(sc_address, key, tx_id, operation_node, op_type, commutativity);
        
        if self.deps[tx_id].as_ref().unwrap().is_empty() {
            // If tx has no dependencies, push to ready queue
            self.execution_queues.push_ready(tx_id);
        }
    }


    /// Updates all the dependency structs, trackers & counters given a dependent_node that depends on a possible dependency_node.
    /// 
    /// This method also pushes the current tx into the partial_ready_queue if this is the first operation, or to the dependency's patial ready
    /// if this is the first operation of this tx & depends on another tx.
    fn set_node_dependency(&mut self, dependent_node: &mut DependencyNode<VecOperation>, dependency_node: Option<NodeRef<VecOperation>>, tid: TxId, first_operation: bool) {
       
        match dependency_node {
            Some(write) => {
                
                // set new operation's dependency on previous write
                dependent_node.set_dependency(Some(Arc::clone(&write)));

                let last_write_op = write.read();
                let last_write_tx_id = last_write_op.data.tx_block_id; 
                let last_write_is_from_this_tx =  last_write_op.data.is_from_tx(tid);
                drop(last_write_op);

                // Last write was made by another tx
                if !last_write_is_from_this_tx {
                    // set our tid as a dependent tx of the tx responsible for the write we need to wait for
                    if !self.dependent_txs.contains_key(&last_write_tx_id) {
                        self.dependent_txs.insert(last_write_tx_id, HashSet::new());
                    }
                    let mut dependent_txs = self.dependent_txs.get_mut(&last_write_tx_id).unwrap();
                    dependent_txs.insert(tid);

                    if first_operation {

                        if !self.partial_ready_tx.contains_key(&last_write_tx_id) {
                            self.partial_ready_tx.insert(last_write_tx_id, HashSet::new());
                        }
                        let mut partial_ready = self.partial_ready_tx.get_mut(&last_write_tx_id).unwrap();

                        partial_ready.insert(tid); 
                    }

                    // Increase dependency count
                    let tx_dependencies = self.deps[tid].as_ref().unwrap();
                    tx_dependencies.insert(last_write_tx_id);
                }
            },
            // No previous write
            None => {
                if first_operation {
                    self.execution_queues.push_partial_ready(tid);
                }
            }
        }

    }

    /// Appends a read operation at the end of the schedule
    /// 
    /// Sets the dependencies for this new read operation. This will depend on some factors:
    /// 
    /// - If Read is Commutative -> then can either depend on a previous NonComm Write, or on storage.
    /// - If Read is Non Commutativ -> then it depends on the most recent write (be it commutative or non commutative), or on storage.
    fn update_schedule_on_read_operation(&mut self, first_operation: bool, tx_id: TxId, 
        contract: ScAddr, key_bytes: &Vec<u8>, commutativity: Commutativity) -> NodeRef<VecOperation> {

        // create a new operation node
        let operation = Operation::new(OpType::Read, tx_id, commutativity, first_operation);
        let mut op_node = DependencyNode::new(operation);

        // create empty schedule for this SC
        self.schedule.create_if_not_exists(contract);

        let LastWrites { commutative, non_commutative  } = self.schedule.get_last_writes(&contract, &key_bytes);

        match commutativity { // TODO refactor this to use the method from LasrWrites
            // If read is commutative -> It can only depend on non commutative writes.
            // There is no conflict between Commutative operations.
            Commutativity::Commutative => {
                // println!("Commutative Read from {:?} depending on: {:?}", tx_id, non_commutative);
                self.set_node_dependency(&mut op_node, non_commutative, tx_id, first_operation);
            },
            Commutativity::NonCommutative => {
                match (&commutative, &non_commutative) {
                    // If there are both a commutative & non commutative writes, pick the operation from the latest tx.
                    (Some(comm), Some(non_comm)) => {
                        let comm_id = comm.read().data.tx_block_id;
                        let non_comm_id = non_comm.read().data.tx_block_id;

                        let dependency = if comm_id > non_comm_id { commutative }
                        else { non_commutative };

                        // println!("NonCommutative Read from {:?} depending on: {:?}", tx_id, dependency);
                        self.set_node_dependency(&mut op_node, dependency, tx_id, first_operation);
                    },
                    // If there is either only a commutative or a non commutative write, pick that one
                    (Some(_), None) => {
                        // println!("NonCommutative Read from {:?} depending on commutative: {:?}", tx_id, commutative);
                        self.set_node_dependency(&mut op_node, commutative, tx_id, first_operation);
                    },
                    (None, Some(_)) => {
                        // println!("NonCommutative Read from {:?} depending on non commutative: {:?}", tx_id, non_commutative);
                        self.set_node_dependency(&mut op_node, non_commutative, tx_id, first_operation);
                    },
                    // No dependency
                    (None, None) => {
                        // println!("NonCommutative Read from {:?} no dependency", tx_id);
                        self.set_node_dependency(&mut op_node, None, tx_id, first_operation);
                    }
                }
            }
        };

        let concurrent_op_node = Arc::new(RwLock::new(op_node));
        self.schedule.append(contract, key_bytes, Arc::clone(&concurrent_op_node), OpType::Read, commutativity);
        concurrent_op_node

    }

    fn update_schedule_on_write_operation(&mut self, first_operation: bool, tx_id: TxId, 
        contract: ScAddr, key_bytes: &Vec<u8>, commutativity: Commutativity) -> NodeRef<VecOperation> {

        // create a new operation node
        let operation = Operation::new(OpType::Write, tx_id, commutativity, first_operation);
        let op_node = DependencyNode::new(operation);

        // create empty schedule for this SC
        self.schedule.create_if_not_exists(contract);

        // append to schedule
        let concurrent_op_node = Arc::new(RwLock::new(op_node));
        self.schedule.append(contract, key_bytes, Arc::clone(&concurrent_op_node), OpType::Write, commutativity);
        if first_operation {
            self.execution_queues.push_partial_ready(tx_id);
        }

        concurrent_op_node
    }

    /// Given a state manager (a struct that keeps info about the state of each SC),
    /// It runs over all SC addresses & keys stored in the schedules, fetches the last non commutative write
    /// node of each & saves the value of that node to storage
    pub fn persist_schedule<A, S, W, Q>(&self, state_manager: &SCManager<A, S, W, Q>) 
    where
        A: BackendApi,
        S: ConcurrentStorage,
        W: StorageWrapper,
        Q: Querier
    {
        // run over each schedule of each SC
        for schedule in &*self {
            let sc_address = *schedule.key();
            let sc_storage = state_manager.get_contract_storage(sc_address);
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
    pub fn set_value(node: &NodeRef<VecOperation>, value: &[u8]) {
        
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
                        let prev_incr_read_val = prev_incr_read.read().data.value.get_value().unwrap();
                        
                        #[cfg(feature = "debug")]
                        print_with_thread_id!("Prev incr read {:?}", prev_incr_read_val);

                        let val = value.to_vec();
                        let delta = val.compute_delta(&prev_incr_read_val);

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
        }
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
        let mut starting_node = Arc::clone(node);
        let mut accumulated_deltas =  vec![];

        // auxilliary function
        let mut merge_accumulated_delta = |delta: Vec<u8>| {
            if accumulated_deltas.is_empty() {
                accumulated_deltas = delta;
            }
            else {
                accumulated_deltas.merge(&delta);
            }
        };

        #[cfg(feature = "debug")]
        print_with_thread_id!("Mergind deltas");

        loop {
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
                merge_accumulated_delta(val);
                break accumulated_deltas;
 
            }
        }
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
        // fetch node info
        let node_read_lock = read_node.read();

        if node_read_lock.data.is_read() {
            if node_read_lock.data.is_commutative() {

                let dependency_val = if let Some(dependency) = &node_read_lock.dependency {
                    let node_lock = dependency.read();
                    // println!("Comm Read depnded on: {:?}", node_lock.data);
                    Some(node_lock.data.wait_for_value())
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
                        Some(node_lock.data.wait_for_value())
                    }
                }
                else {
                    concurrent_storage.get_uncharged(key)
                }
            }
        }
        else {
            panic!("This method should only be called for read nodes!")
        }
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
    use std::sync::{atomic::Ordering, Arc};

    use serial_test::serial;
    use wasmer::Store;

    use crate::{
        internals::instance_from_module, symb_exec::{Commutativity, Key, ReadWrite, StorageDependency, TxRWS}, testing::{
            mock_concurrent_backend, mock_persistent_backend, mock_tx_operation, 
            ConcurrentStorage, MockApi, MockConcurrentStorage, MockQuerier, MockStorageWrapper
        }, vm_manager::{
            concurrent_schedule::LastWrites, schedule::{OperationValue, ScAddr}, vm_manager::{InstantiatedEntryPoint, RWSContext, VMMessage}
        }, wasm_backend::{compile, make_compiling_engine}, ConcurrentSchedule, InstanceOptions, SCManager, SEStatus, Size
    };

    use super::{DependencyNode, NodeRef, OpType, VecOperation};

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");
    const SC_ADDR_A: ScAddr = *b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
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

    fn mock_state_manager(sc_address: ScAddr) -> SCManager<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier> {
        // create a state manager
        let state_manager: SCManager<MockApi, MockConcurrentStorage, MockStorageWrapper, MockQuerier> = SCManager::new();
        state_manager.save_code(CONTRACT).unwrap();

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


        state_manager.save_instance(0, sc_address, backend, instances);
        
        state_manager
    }

    #[test]
    #[serial]
    fn concurrent_schedule_build() {
        let mut concurrent_schedule = ConcurrentSchedule::new();
        let mut block = vec![
            mock_tx_operation(SC_ADDR_A, &vec![1u8], 1, ReadWrite::write(), Commutativity::Commutative),
        ];

        concurrent_schedule.build_from_rws(&mut block);

        let deps = concurrent_schedule.deps;
        // tx_block_id should have 0 dependencies
        assert_eq!(deps[1].as_ref().unwrap().len(), 0);
        
        // pop only available tx - tx with id 1
        let ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), 1);

        let partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
        let mut locked_partial = partial_ready_q.lock();
        assert!(locked_partial.pop_front().is_none());

        // check if operation node has been set
        let rws = block.get(0).unwrap().rws.rws.get(0).unwrap(); 
        match rws {
            ReadWrite::Read { .. } => assert!(false),
            ReadWrite::Write { operation_node, .. } => {
                assert!(operation_node.is_some());
            }
        }
    }

    #[test]
    #[serial]
    fn concurrent_schedule_build_complex_ex() {
        let key_a = vec![1u8];
        let key_b = vec![2u8];
        let key_c = vec![3u8];
        let key_d = vec![4u8];

        let tx1 = 1;
        let tx2 = 2;
        let tx3 = 3;
        let tx4 = 4;
        let tx5 = 5;
        let tx6 = 6;

        let mut concurrent_schedule = ConcurrentSchedule::new();
        concurrent_schedule.build_from_rws(&mut vec![

            // Tx1: R(A), W(A), W(B), R(C), W(C)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: tx1,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "A".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_a.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_a.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_b.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_c.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_c.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },

            // Tx2: R(D), W(A), R(B), W(B)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: tx2,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "B".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_d.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_a.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_b.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_b.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },

            // Tx3: R(A), W(A)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: tx3,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "C".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_a.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_a.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },

            // Tx4: R(C), W(C)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: tx4,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "D".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_c.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_c.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },

            // Tx5: R(B), W(B)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: tx5,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "E".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_b.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_b.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },

            // Tx6: R(D), W(D)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: tx6,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "F".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_d.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_d.clone()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },
        ]);


        // Final Expected Schedule:

        //  |<---------------------------|                         
        // A|<-[T1: R(A)]-[T1: W(A)]    [T2: W(A)]            <- [T3: R(A)]-[T3: W(A)]
        //  |
        // B|<-[T1: W(B)]            <- [T2: R(B)]-[T2: W(B)] <- [T5: R(B)]-[T5: W(B)]
        //  |
        // C|<-[T1: R(C)]-[T1: W(C)] <- [T4: R(C)]-[T4: W(C)]
        //  |
        // D|<-[T2: R(D)]            <- [T6: R(D)]-[T6: W(D)]

        // println!("{:#?}", concurrent_schedule);

        let deps = concurrent_schedule.deps;
        assert_eq!(deps[tx1].as_ref().unwrap().len(), 0);
        assert_eq!(deps[tx2].as_ref().unwrap().len(), 1);
        assert_eq!(deps[tx3].as_ref().unwrap().len(), 1);
        assert_eq!(deps[tx4].as_ref().unwrap().len(), 1);
        assert_eq!(deps[tx5].as_ref().unwrap().len(), 1);
        assert_eq!(deps[tx6].as_ref().unwrap().len(), 0);
        
        // READY: { Tx1, Tx6 }
        let ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), tx1);
        assert_eq!(ready_q.lock().pop_front().unwrap(), tx6);

        // PARTIAL_READY: { Tx2 }
        let partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
        let mut locked_partial = partial_ready_q.lock();
        assert_eq!(locked_partial.pop_front().unwrap(), tx2);


        let dependent_txs = concurrent_schedule.dependent_txs;
        // Tx2 & Tx4 depend on Tx1
        assert!(dependent_txs.get(&tx1).unwrap().contains(&tx2));
        assert!(dependent_txs.get(&tx1).unwrap().contains(&tx4));
        // Tx3 & Tx5 depend on Tx2
        assert!(dependent_txs.get(&tx2).unwrap().contains(&tx3));
        assert!(dependent_txs.get(&tx2).unwrap().contains(&tx5));
        // Tx3-6 have no dependencies
        assert!(dependent_txs.get(&tx3).is_none());
        assert!(dependent_txs.get(&tx4).is_none());
        assert!(dependent_txs.get(&tx5).is_none());
        assert!(dependent_txs.get(&tx6).is_none());

        let ready_partials = concurrent_schedule.partial_ready_tx;
        // Tx1 has T4 as ready partial
        assert!(ready_partials.get(&tx1).unwrap().contains(&tx4));
        // Tx2 has Tx3 & Tx5 as ready_partial
        assert!(ready_partials.get(&tx2).unwrap().contains(&tx3));
        assert!(ready_partials.get(&tx2).unwrap().contains(&tx5));
    }

    // Storage | <- [Non Comm Read]
    #[test]
    #[serial]
    fn get_value_non_commutative_depends_on_storage() {
        let key = vec![0u8];
        let val = "100".as_bytes().to_vec();

        let mut concurrent_schedule = ConcurrentSchedule::new();
        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A, &key, 1, ReadWrite::read(), Commutativity::NonCommutative),

        ];

        concurrent_schedule.build_from_rws(&mut rws);
        let operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let node = match operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());
        concurrent_storage.set(key.as_slice(), val.as_slice()).0.unwrap(); 


        let read_val = concurrent_schedule.get_value(node, &concurrent_storage, &SC_ADDR_A, &key);

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

        let mut concurrent_schedule = ConcurrentSchedule::new();
        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A, &key, 1, ReadWrite::read(), Commutativity::Commutative),

        ];

        concurrent_schedule.build_from_rws(&mut rws);
        let operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let node = match operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());
        concurrent_storage.set(key.as_slice(), val.as_slice()).0.unwrap(); 


        let read_val = concurrent_schedule.get_value(node, &concurrent_storage, &SC_ADDR_A, &key);

        assert_eq!(read_val, Some(val.clone()));
        assert_eq!(node.read().data.value.get_value(), Some(val));
    }

    // Storage | <- [Comm Read] <- [Comm Write]
    // Should update the value read in the node
    #[test]
    #[serial]
    fn set_value_commutative_depends_on_commutative_read() {
        let key = vec![0u8];
        let val = "100".as_bytes().to_vec();

        let mut concurrent_schedule = ConcurrentSchedule::new();
        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A, &key, 1, ReadWrite::read(),  Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A, &key, 1, ReadWrite::write(), Commutativity::Commutative),

        ];

        concurrent_schedule.build_from_rws(&mut rws);
                
        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());
        concurrent_storage.set(key.as_slice(), val.as_slice()).0.unwrap();

        // read node
        let operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let node = match operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        concurrent_schedule.get_value(node, &concurrent_storage, &SC_ADDR_A, &key);

        // write node
        let operation = rws.get(1).unwrap().rws.rws.get(0).unwrap();
        let node = match operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
 
        ConcurrentSchedule::set_value(node, "105".as_bytes());

        // write commutative node should end up having the delta -> 105 - 100 = 5
        assert_eq!(node.read().data.value.get_value(), Some("5".as_bytes().to_vec()));
    }

    // Storage | [Non Comm Write] <- [Non Comm Read]
    #[test]
    #[serial]
    fn get_value_non_commutative_depends_on_non_commutative_write() {
        let key = vec![0u8];
        let val = "100".as_bytes().to_vec();

        let mut concurrent_schedule = ConcurrentSchedule::new();
        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A, &key, 1, ReadWrite::write(), Commutativity::NonCommutative),
            mock_tx_operation(SC_ADDR_A, &key, 2, ReadWrite::read(),  Commutativity::NonCommutative),
        ];

        concurrent_schedule.build_from_rws(&mut rws);

        let write_operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };

        ConcurrentSchedule::set_value(write_node, &val);

        let read_operation = rws.get(1).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());

        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A, &key);

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

        let mut concurrent_schedule = ConcurrentSchedule::new();
        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A, &key, 1, ReadWrite::read(), Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A, &key, 1, ReadWrite::write(), Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A, &key, 2, ReadWrite::read(),  Commutativity::NonCommutative),
        ];

        concurrent_schedule.build_from_rws(&mut rws);

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());
        concurrent_storage.set(key.as_slice(), val.as_slice()).0.unwrap();

        // Comm read -> read X
        let read_operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A, &key);
        assert_eq!(read_val, Some(val));

        // Comm write -> write Z = Y - X
        let write_operation = rws.get(1).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        ConcurrentSchedule::set_value(write_node, &comm_write);
        assert_eq!(write_node.read().data.value.get_value(), Some(delta));

        // NonComm read -> read X + Z = Y
        let read_operation = rws.get(2).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A, &key);

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

        let mut concurrent_schedule = ConcurrentSchedule::new();
        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A, &key, 1, ReadWrite::write(), Commutativity::NonCommutative),
            mock_tx_operation(SC_ADDR_A, &key, 2, ReadWrite::read(),  Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A, &key, 2, ReadWrite::write(), Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A, &key, 3, ReadWrite::read(),  Commutativity::NonCommutative),
        ];

        concurrent_schedule.build_from_rws(&mut rws);

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());

        // NonComm write -> write X
        let write_operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        ConcurrentSchedule::set_value(write_node, val.as_slice());
        assert_eq!(write_node.read().data.value.get_value(), Some(val.clone()));

        // Comm read -> read X
        let read_operation = rws.get(1).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A, &key);
        assert_eq!(read_val, Some(val));

        // Comm write -> write Z = Y - X
        let write_operation = rws.get(2).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        ConcurrentSchedule::set_value(write_node, &comm_write);
        assert_eq!(write_node.read().data.value.get_value(), Some(delta));

        // NonComm read -> read X + Z = Y
        let read_operation = rws.get(3).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A, &key);

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

        let mut concurrent_schedule = ConcurrentSchedule::new();
        let mut rws = vec![
            mock_tx_operation(SC_ADDR_A, &key, 1, ReadWrite::read(),  Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A, &key, 1, ReadWrite::write(), Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A, &key, 2, ReadWrite::read(),  Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A, &key, 2, ReadWrite::write(), Commutativity::Commutative),
            mock_tx_operation(SC_ADDR_A, &key, 3, ReadWrite::read(),  Commutativity::NonCommutative),
        ];

        concurrent_schedule.build_from_rws(&mut rws);

        let concurrent_storage: Arc<dyn ConcurrentStorage> = Arc::new(MockConcurrentStorage::new());
        concurrent_storage.set(key.as_slice(), val.as_slice()).0.unwrap();

        // Comm read1
        let read_operation = rws.get(0).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A, &key);
        assert_eq!(read_val, Some(val.clone()));

        // Comm write1
        let write_operation = rws.get(1).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        ConcurrentSchedule::set_value(write_node, &comm_write1);
        assert_eq!(write_node.read().data.value.get_value(), Some(delta1));

        // Comm read2
        let read_operation = rws.get(2).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A, &key);
        assert_eq!(read_val, Some(val));

        // Comm write2
        let write_operation = rws.get(3).unwrap().rws.rws.get(0).unwrap();
        let write_node = match write_operation { 
            ReadWrite::Write { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        ConcurrentSchedule::set_value(write_node, &comm_write2);
        assert_eq!(write_node.read().data.value.get_value(), Some(delta2));

        // NonComm read
        let read_operation = rws.get(4).unwrap().rws.rws.get(0).unwrap();
        let read_node = match read_operation { 
            ReadWrite::Read { operation_node, .. } => operation_node.as_ref().unwrap(),
            _ => unreachable!("")
        };
        let read_val = concurrent_schedule.get_value(read_node, &concurrent_storage, &SC_ADDR_A, &key);

        assert_eq!(read_val, Some(final_val));
    }


    #[test]
    #[serial]
    fn untracked_write_no_dependencies() {
        let sc_address = SC_ADDR_A;
        let key = vec![1u8];

        let mut concurrent_schedule = ConcurrentSchedule::new();
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(sc_address, &vec![2u8], 1, ReadWrite::write(), Commutativity::NonCommutative),
        ]);
        
        // insert untracked write
        let op_node = DependencyNode::new_ref(OpType::Write, 1, Commutativity::NonCommutative, true);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node));

        // tx1 has no dependencies
        let deps = concurrent_schedule.deps;
        assert_eq!(deps[1].as_ref().unwrap().len(), 0);

        // added to ready queue
        let ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), 1);

        // not added to partial_ready
        let partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
        assert!(partial_ready_q.lock().pop_front().is_none());

        // schedule head is the write node
        let sc_schedule = concurrent_schedule.schedule.schedule.get(&sc_address).unwrap();
        let head = &sc_schedule.get(&key).unwrap().head;
        assert_eq!(*head.read().read(), *op_node.read());

        // schedule tail is the write node
        let tail = &sc_schedule.get(&key).unwrap().tail;
        assert_eq!(*tail.read().read(), *op_node.read());

        // schedule last_non_commutative write is the write node
        let LastWrites {commutative, non_commutative } = concurrent_schedule.schedule.get_last_writes(&sc_address, &key);

        match (commutative, non_commutative) {
            (None, Some(non_comm)) => {
                assert_eq!(*non_comm.read(), *op_node.read());
            },
            _ => assert!(false)
        }
        
    }

    #[test]
    #[serial]
    fn untracked_read_with_dependency_on_write_same_tx() {
        let sc_address = SC_ADDR_A;
        let key = vec![1u8];

        let mut concurrent_schedule = ConcurrentSchedule::new();
        
        // random read write just for the txs to have at least 1 read/write
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(SC_ADDR_A, &vec![2u8], 1, ReadWrite::write(), Commutativity::NonCommutative),
        ]);
        
        // insert untracked write
        let op_node_write = DependencyNode::new_ref(OpType::Write, 1, Commutativity::NonCommutative, true);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node_write));

        // insert untracked read
        let op_node_read = DependencyNode::new_ref(OpType::Read, 1, Commutativity::NonCommutative, false);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node_read));

        // tx has no dependencies
        let deps = concurrent_schedule.deps;
        assert_eq!(deps[1].as_ref().unwrap().len(), 0);

        // tx is in ready queue
        let ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), 1);

        // tx is not in partial_ready
        let partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
        assert!(partial_ready_q.lock().pop_front().is_none());

        // head is the 1st write operation
        let sc_schedule = concurrent_schedule.schedule.schedule.get(&sc_address).unwrap();
        let head = &sc_schedule.get(&key).unwrap().head;
        assert_eq!(*head.read().read(), *op_node_write.read());

        // tail is the last read operation
        let tail = &sc_schedule.get(&key).unwrap().tail;
        assert_eq!(*tail.read().read(), *op_node_read.read());

        // write operation's next value is the read operation
        assert_node_next(&op_node_write, &op_node_read);

        // read operation's prev value is the read operation
        assert_node_prev(&op_node_read, &op_node_write);

        // read operation's dependency should be set to the write node
        assert_node_dependency(&op_node_read, &op_node_write);

    }

    #[test]
    #[serial]
    fn untracked_read_with_dependency_on_write_different_tx() {
        let sc_address = SC_ADDR_A;
        let key = vec![1u8];

        let mut concurrent_schedule = ConcurrentSchedule::new();

        // each tx must have at least 1 RW - inside the schedule we pre-allocate a vector with the size of 
        // the number of different txs - and we only count txs by their RWS
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(SC_ADDR_A, &vec![2u8], 1, ReadWrite::write(), Commutativity::NonCommutative),
            mock_tx_operation(SC_ADDR_A, &vec![3u8], 2, ReadWrite::read(),  Commutativity::NonCommutative),
        ]);
        
        // insert untracked write
        let op_node_write = DependencyNode::new_ref(OpType::Write, 1, Commutativity::NonCommutative, true);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node_write));

        // insert untracked read
        let op_node_read = DependencyNode::new_ref(OpType::Read, 2, Commutativity::NonCommutative, true);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node_read));

        // tx1 has no dependencies
        let deps = concurrent_schedule.deps;
        assert_eq!(deps[1].as_ref().unwrap().len(), 0);

        // tx2 has no dependencies - recall we are simulating running time - an untracked operations is only 'tracked' when the tx is
        // executing. And if it started executing, is beacause it was either in READY or PARTIAL_READY queue, so it had no dependencies.
        // Even if it now depends on tx1, the operation itself will need to wait on tx1's operation, but still, tx2 is not marked
        // to have any dependencies since it already started executing.
        assert_eq!(deps[2].as_ref().unwrap().len(), 0);

        // here we are checking only on the original RWS - the tx placement in the queues does not count for untracked RWS
        // tx1 is in ready queue
        let ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), 1);
        // tx2 is in ready queue
        assert_eq!(ready_q.lock().pop_front().unwrap(), 2);

        // tx1 nor tx2 are in partial_ready
        let partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
        assert!(partial_ready_q.lock().pop_front().is_none());

        // head is the 1st write operation
        let sc_schedule = concurrent_schedule.schedule.schedule.get(&sc_address).unwrap();
        let head = &sc_schedule.get(&key).unwrap().head;
        assert_eq!(*head.read().read(), *op_node_write.read());

        // tail is the last read operation
        let tail = &sc_schedule.get(&key).unwrap().tail;
        assert_eq!(*tail.read().read(), *op_node_read.read());

        // write operation's next value is the read operation
        assert_node_next(&op_node_write, &op_node_read);

        // read operation's prev value is the read operation
        assert_node_prev(&op_node_read, &op_node_write);

        // read operation's dependency should be set to the write node
        assert_node_dependency(&op_node_read, &op_node_write);

    }

    #[test]
    #[serial]
    fn perfect_rws_persist_storage() {
        let write_key = vec![1u8];
        let val = vec![12u8];
        let sc_address = SC_ADDR_A;

        let mut concurrent_schedule = ConcurrentSchedule::new();
        let mut block = vec![
            mock_tx_operation(sc_address, &write_key, 1, ReadWrite::write(), Commutativity::NonCommutative),
        ];

        // build schedule
        concurrent_schedule.build_from_rws(&mut block);

        // get write node
        let schedule = &concurrent_schedule.schedule.schedule;
        let sc_schedule = schedule.get(&sc_address).unwrap();
        let linked_list = sc_schedule.get(&write_key).unwrap();
        let write_operation = linked_list.head.read();

        // set write node's value
        ConcurrentSchedule::set_value(&*write_operation, val.as_slice());

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
        let sc_address = SC_ADDR_A;
        let key = vec![1u8];

        let mut concurrent_schedule = ConcurrentSchedule::new();
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(sc_address, &key, 1, ReadWrite::write(), Commutativity::NonCommutative),
        ]);
        
        // insert untracked write
        let op_node_write = DependencyNode::new_ref(OpType::Write, 1, Commutativity::NonCommutative, true);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node_write));
        
        concurrent_schedule.get_next_message_to_execute();
        concurrent_schedule.on_tx_finish(&RWSContext {
            rws: TxRWS {
                storage_dependency: StorageDependency::Independent,
                profile_status: SEStatus::Complete,
                rws_uid: "A".to_owned(),
                rws: vec![],
            },
            address: SC_ADDR_A,
            tx_message: None,
            tx_block_id: 0
        });

        let deps = &concurrent_schedule.deps;
        assert_eq!(deps[1 as usize].as_ref().unwrap().len(), 0);
    }

}