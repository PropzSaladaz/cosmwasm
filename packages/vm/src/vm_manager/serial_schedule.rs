use std::{
    collections::{BTreeMap, HashMap, HashSet, VecDeque}, sync::{atomic::{AtomicUsize, Ordering}, mpsc, Arc}, thread, time::{Duration, Instant}
};

use parking_lot::{Mutex, Condvar, RwLock};

use crate::{print_with_thread_id, symb_exec::{Commutativity, Key, ReadWrite}, testing::{ConcurrentStorage, StorageWrapper}, vm_manager::schedule::MergeableValue, BackendApi, Querier, SCManager};

use super::{schedule::{DependencyNode, NodeRef, OpType, Operation, SCSchedule, ScAddr, TxId, VecOperation}, vm_manager::RWSContext, LastWrites, Schedule, TxState};

#[cfg(feature = "debug_graph")]
use super::dot_schedule::{DotSchedule, NodeColor};

#[derive(Debug)]
pub struct SerialQueues {
    pub executed_txs: TxId,
    pub total_txs: TxId,
    pub ready_queue: VecDeque<TxId>,
    pub partial_ready_queue: VecDeque<TxId>,
}

impl PartialEq for SerialQueues {
    fn eq(&self, other: &Self) -> bool {
        self.executed_txs ==  other.executed_txs &&
        self.total_txs == other.total_txs &&
        self.ready_queue == other.ready_queue &&
        self.partial_ready_queue == other.partial_ready_queue
    }
}

impl SerialQueues {
    fn new() -> SerialQueues {
        SerialQueues {
            executed_txs: 0,

            total_txs: 0,

            ready_queue: VecDeque::new(),
            partial_ready_queue: VecDeque::new(),
        }
    }

    /// Merges 2 concurrent queues assuming that the 'other' queue already has an updated
    /// ready & partial_ready queues accounting for the merged state of both schedules.
    /// 
    /// If schedule A has a TxA operation on key 1, then 'other' queue should not have
    /// any tx with an operation on key 1 placed in the ready_queue (this validation must be done outside this method)
    fn merge(&mut self, other: SerialQueues) {
        self.total_txs = self.total_txs + other.total_txs;
        
        // TODO - refactor
        let ready = other.ready_queue;
        let partial_ready = other.partial_ready_queue;

        self.ready_queue.extend(ready);
        self.partial_ready_queue.extend(partial_ready);
    }

    fn remove_id_from_ready(&mut self, id: TxId) -> Option<TxId> {
        if let Some(pos) = self.ready_queue.iter().position(|&x| x == id) {
            self.ready_queue.remove(pos)
        } else { None }
    }

    fn remove_id_from_partial_ready(&mut self, id: TxId) {
        if let Some(pos) = self.partial_ready_queue.iter().position(|&x| x == id) {
            self.partial_ready_queue.remove(pos);
        }
    }

    fn set_total_txs(&mut self, total_txs: TxId) {
        self.total_txs = total_txs;
    }

    fn push_ready(&mut self, ready: TxId) {
        self.ready_queue.push_back(ready);
    }

    fn push_partial_ready(&mut self, partial_ready: TxId) {
        self.partial_ready_queue.push_back(partial_ready);
    }
}


#[derive(Debug)]
pub struct ScheduleBuilder {
    /// Stores state of each tx - Executing, Executed, NotExecuted - This is used when finishing tx execution.
    /// We update the dependencies of all txs that depend on the one we finished executing & then we use the tx status
    /// to filter when to push a tx that has no dependencies & hasn't started executing yet
    pub tx_states: Vec<TxState>,

    // Set with an Id for each tx in the block
    pub transactions: HashSet<TxId>,

    /// Total number of txs in the block
    pub total: TxId,

    /// Stores the id of txs that are the dependencies of some TxId
    pub deps: BTreeMap<TxId, HashSet<TxId>>,

    /// stores the txs that depend on some tx
    /// Tx -> Set of txs depending on it
    pub dependent_txs: BTreeMap<TxId, HashSet<TxId>>,

    /// stores the txs that have their 1st operation depending on it
    /// Tx -> Set of txs which their 1st operation depends on this tx
    pub partial_ready_tx: BTreeMap<TxId, HashSet<TxId>>,

    /// Signal used when any tx is pushed either to READY or PARTIAL_READY queue
    pub execution_queues: SerialQueues,

    /// mapping of SC_address -> key -> linked list of operations
    pub schedule: Schedule,

    // #[cfg(feature="exec_time")]
    node_dependency_timer: Option<Instant>,
    node_dependency_time: Duration,

    node_creation_timer: Option<Instant>,
    node_creation_time: Duration,
}

/// Iterator that allows iterating over each schdule/contract address
impl<'a> IntoIterator for &'a ScheduleBuilder {
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

impl PartialEq for ScheduleBuilder {
    fn eq(&self, other: &ScheduleBuilder) -> bool {
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

impl ScheduleBuilder {
    fn compare_deps(&self, other: &ScheduleBuilder) -> bool {
        if self.deps.len() != other.deps.len() { return false; }
        
        self.deps.iter().all(|(key, set1)| {
            match other.deps.get(key) {
                Some(set2) => {
                    set1.len() == set2.len() && 
                    set1.iter().all(|item| set2.contains(item))
                },
                None => false,
            }
        })
    }

    fn compare_dependent_txs(&self, other: &ScheduleBuilder) -> bool {
        if self.dependent_txs.len() != other.dependent_txs.len() { return false; }
        
        self.dependent_txs.iter().all(|(key, set1)| {
            match other.dependent_txs.get(key) {
                Some(set2) => {
                    set1.len() == set2.len() && 
                    set1.iter().all(|item| set2.contains(item))
                },
                None => false,
            }
        })
    }

    fn compare_partial_ready_tx(&self, other: &ScheduleBuilder) -> bool {
        if self.partial_ready_tx.len() != other.partial_ready_tx.len() { return false; }
        
        self.partial_ready_tx.iter().all(|(key, set1)| {
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

impl ScheduleBuilder {
    pub fn new() -> Self {
        ScheduleBuilder {
            tx_states: vec![],
            total: 0,

            transactions: HashSet::new(),

            deps: BTreeMap::new(),

            execution_queues: SerialQueues::new(),
            
            schedule: Schedule::new(),
            
            dependent_txs: BTreeMap::new(),

            partial_ready_tx: BTreeMap::new(),

            // #[cfg(feature = "exec_time")]
            node_dependency_timer: None,
            // #[cfg(feature = "exec_time")]
            node_dependency_time: Duration::ZERO,
            // #[cfg(feature = "exec_time")]
            node_creation_timer: None,
            // #[cfg(feature = "exec_time")]
            node_creation_time: Duration::ZERO,
        }
    }

    // #[cfg(feature = "exec_time")]
    fn start_node_dependency_timer(&mut self) {
        self.node_dependency_timer = Some(Instant::now());
    }

    // #[cfg(feature = "exec_time")]
    fn stop_node_dependency_timer(&mut self) {
        let elapsed = self.node_dependency_timer.unwrap().elapsed();
        self.node_dependency_time += elapsed;
    }

    // #[cfg(feature = "exec_time")]
    fn start_node_creation_timer(&mut self) {
        self.node_creation_timer = Some(Instant::now());
    }

    // #[cfg(feature = "exec_time")]
    fn stop_node_creation_timer(&mut self) {
        let elapsed = self.node_creation_timer.unwrap().elapsed();
        self.node_creation_time += elapsed;
    }

    /// Builds an execution schedule from a sequence of RWS's per messages.
    /// Run over each RWS & insert it in the schedule marking the dependencies between operations & transactions
    pub fn build_from_rws(&mut self, block: &mut Vec<RWSContext>) {

        self.total = block.len() as TxId;

        self.execution_queues.set_total_txs(self.total);
        self.tx_states = vec![TxState::NotExecuted ; self.total];

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

            if self.deps.entry(tx_id).or_insert(HashSet::new()).is_empty() { // no dependencies
                self.execution_queues.push_ready(tx_id);
                self.execution_queues.remove_id_from_partial_ready(tx_id);
            }
        }

        // #[cfg(feature = "exec_time")]
        // {
        //     print_with_thread_id!("Schedule Build times -------");
        //     print_with_thread_id!("Node creation time: {:?}", self.node_creation_time);
        //     print_with_thread_id!("Node depdency setting time: {:?}", self.node_dependency_time);
        // }
    }

    /// Merge the state from 2 sequential partial schedules. The 'other' schedule is assumed to come after
    /// the 'self' schedule.
    /// 
    /// Set the dependencies of the first operations from the 'other' schedule as the last writes from the 
    /// 'self' schedule, update the 'prev' and 'next' fields of the nodes & update the ready & partial ready queues.
    pub fn merge(&mut self, mut other: ScheduleBuilder) {
        self.total = self.total + other.total;

        self.tx_states = vec![TxState::NotExecuted ; self.total];
        self.deps.extend(other.deps);
        self.dependent_txs.extend(other.dependent_txs);
        self.partial_ready_tx.extend(other.partial_ready_tx);
        self.transactions.extend(other.transactions);

        self.schedule.merge(other.schedule, &mut | node_self: NodeRef<VecOperation>, node_other: NodeRef<VecOperation>| {
            let node_other_tx_id = node_other.read().data.tx_block_id;
            let node_self_tx_id = node_self.read().data.tx_block_id; 
            
            self.deps.entry(node_other_tx_id).or_insert(HashSet::new()).insert(node_self_tx_id);
            self.dependent_txs.entry(node_self_tx_id).or_insert(HashSet::new()).insert(node_other_tx_id);
            
            let ready_tx = other.execution_queues.remove_id_from_ready(node_other_tx_id);

            // if is first operation of some tx from 'other' schedule, then remove it the 'other's from partial_ready_queue &
            // add it to the partial ready of the tx from the 'self' schedule  
            if node_other.read().data.first_operation {
                other.execution_queues.remove_id_from_partial_ready(node_other_tx_id);
                self.partial_ready_tx.entry(node_self_tx_id).or_insert(HashSet::new()).insert(node_other_tx_id);
            }
            // Was not first operation && was still in ready 
            // (meaning no other previous operation had a dependency) - inisert in partial_ready 
            else if let Some(tx) = ready_tx {
                self.execution_queues.push_partial_ready(tx);
            }
        });

        self.execution_queues.merge(other.execution_queues);

    }


    /// Updates all the dependency structs, trackers & counters given a dependent_node that depends on a possible dependency_node.
    /// 
    /// This method also pushes the current tx into the partial_ready_queue if this is the first operation, or to the dependency's patial ready
    /// if this is the first operation of this tx & depends on another tx.
    fn set_node_dependency(&mut self, dependent_node: &mut DependencyNode<VecOperation>, dependency_node: Option<NodeRef<VecOperation>>, tid: TxId, first_operation: bool) {
        // #[cfg(feature = "exec_time")]
        self.start_node_dependency_timer();
        
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
                    let dependent_txs = self.dependent_txs.get_mut(&last_write_tx_id).unwrap();
                    dependent_txs.insert(tid);

                    if first_operation {

                        if !self.partial_ready_tx.contains_key(&last_write_tx_id) {
                            self.partial_ready_tx.insert(last_write_tx_id, HashSet::new());
                        }
                        let partial_ready = self.partial_ready_tx.get_mut(&last_write_tx_id).unwrap();

                        partial_ready.insert(tid); 
                    }

                    // Increase dependency count
                    if !self.deps.contains_key(&tid) {
                        self.deps.insert(tid, HashSet::new());
                    }
                    let tx_dependencies = self.deps.get_mut(&tid).unwrap();

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

        // #[cfg(feature = "exec_time")]
        self.stop_node_dependency_timer();


    }

    /// Appends a read operation at the end of the schedule
    /// 
    /// Sets the dependencies for this new read operation. This will depend on some factors:
    /// 
    /// - If Read is Commutative -> then can either depend on a previous NonComm Write, or on storage.
    /// - If Read is Non Commutativ -> then it depends on the most recent write (be it commutative or non commutative), or on storage.
    fn update_schedule_on_read_operation(&mut self, first_operation: bool, tx_id: TxId, 
        contract: ScAddr, key_bytes: &Vec<u8>, commutativity: Commutativity) -> NodeRef<VecOperation> {

        // #[cfg(feature = "exec_time")]
        self.start_node_creation_timer();

        // create a new operation node
        let operation = Operation::new(OpType::Read, tx_id, commutativity, first_operation);
        let mut op_node = DependencyNode::new(operation);

        // create empty schedule for this SC
        self.schedule.create_if_not_exists(contract);

        let LastWrites { commutative, non_commutative  } = self.schedule.get_last_writes(&contract, &key_bytes);

        // #[cfg(feature = "exec_time")]
        self.stop_node_creation_timer();

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

        // #[cfg(feature = "exec_time")]
        self.start_node_creation_timer();

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

        // #[cfg(feature = "exec_time")]
        self.stop_node_creation_timer();

        concurrent_op_node
    }

    #[cfg(feature = "debug_graph")]
    pub fn generate_debug_graph(&self, graph_name: String, rws:  &Arc<Vec<RWSContext>>) {
        let mut dot = DotSchedule::new(NodeColor::LightBlue, 2);

        let dot_file = dot.parse(self, &rws);
        dot.save_as_png(dot_file, graph_name).unwrap();
    }

}