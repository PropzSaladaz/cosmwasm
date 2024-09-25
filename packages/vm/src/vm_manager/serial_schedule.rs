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

    /// Id of the first transaction. This is used to index the correct vector position, as
    /// a tx id from the subset of txs for the current schedule may be larger than the total number
    /// of txs assigned to the current schedule. Thus we use this to subtract & confine the txs index
    /// to a [0, n] interval 
    starting_tx_id: TxId,

    // Set with an Id for each tx in the block
    pub transactions: HashSet<TxId>,

    /// Total number of txs in the block
    pub total: TxId,

    /// Stores the id of txs that are the dependencies of some TxId
    pub deps: Vec<Option<HashSet<TxId>>>,

    /// stores the txs that depend on some tx
    /// Tx -> Set of txs depending on it
    pub dependent_txs: Vec<Option<HashSet<TxId>>>,

    /// stores the txs that have their 1st operation depending on it
    /// Tx -> Set of txs which their 1st operation depends on this tx
    pub partial_ready_tx: Vec<Option<HashSet<TxId>>>,

    /// Signal used when any tx is pushed either to READY or PARTIAL_READY queue
    pub execution_queues: SerialQueues,

    /// mapping of SC_address -> key -> linked list of operations
    pub schedule: Schedule,

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
        
        // self.deps.iter().all(|(key, set1)| {
        //     match other.deps.get(key) {
        //         Some(set2) => {
        //             set1.len() == set2.len() && 
        //             set1.iter().all(|item| set2.contains(item))
        //         },
        //         None => false,
        //     }
        // })
        todo!()
    }

    fn compare_dependent_txs(&self, other: &ScheduleBuilder) -> bool {
        if self.dependent_txs.len() != other.dependent_txs.len() { return false; }
        
        // self.dependent_txs.iter().all(|(key, set1)| {
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

    fn compare_partial_ready_tx(&self, other: &ScheduleBuilder) -> bool {
        if self.partial_ready_tx.len() != other.partial_ready_tx.len() { return false; }
        
        // self.partial_ready_tx.iter().all(|(key, set1)| {
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

impl ScheduleBuilder {
    pub fn new() -> Self {
        ScheduleBuilder {
            tx_states: vec![],
            total: 0,

            starting_tx_id: 0,

            transactions: HashSet::new(),

            deps: Vec::new(),

            execution_queues: SerialQueues::new(),
            
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

    /// Builds an execution schedule from a sequence of RWS's per messages.
    /// Run over each RWS & insert it in the schedule marking the dependencies between operations & transactions
    pub fn build_from_rws(&mut self, block: &mut Vec<RWSContext>) {

        self.total = block.len() as TxId;
        self.starting_tx_id = block[0].tx_block_id;
        
        self.deps = vec![None; self.total];
        self.dependent_txs = vec![None; self.total];
        self.partial_ready_tx = vec![None; self.total];
        
        self.execution_queues.set_total_txs(self.total);
        self.tx_states = vec![TxState::NotExecuted ; self.total];

        for tx in block {

            let mut first_operation = true;
            let tx_id = tx.tx_block_id;
            let contract = &tx.address;

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

            if self.deps[self.tx_id_to_index(tx_id)].is_none() { // no dependencies
                self.execution_queues.push_ready(tx_id);
                self.execution_queues.remove_id_from_partial_ready(tx_id);
            }
        }

        #[cfg(feature = "exec_time")]
        {
            print_with_thread_id!("Schedule Build times -------");
            print_with_thread_id!("Node creation time: {:?}", self.node_creation_time);
            print_with_thread_id!("Node depdency setting time: {:?}", self.node_dependency_time);
        }
    }

    fn tx_id_to_index(&self, tx_id: TxId) -> usize {
        tx_id - self.starting_tx_id
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
            let node_other_lock = node_other.read();
            let node_other_is_non_comm_read = !node_other_lock.data.is_commutative() && node_other_lock.data.is_read();
            let node_other_is_first_operation = node_other_lock.data.first_operation;
            let node_other_tx_id = node_other_lock.data.tx_block_id;
            drop(node_other_lock);
            let node_self_tx_id = node_self.read().data.tx_block_id; 

            // println!("Dependency between schedules: {:?} depends on {:?}", node_other_tx_id, node_self_tx_id);

            let node_other_normalized_idx = node_other_tx_id - self.starting_tx_id;
            let node_self_normalized_idx = node_self_tx_id - self.starting_tx_id;

            self.deps[node_other_normalized_idx].get_or_insert(HashSet::new()).insert(node_self_tx_id);
            self.dependent_txs[node_self_normalized_idx].get_or_insert(HashSet::new()).insert(node_other_tx_id);

            let ready_tx = other.execution_queues.remove_id_from_ready(node_other_tx_id);

            if node_other_is_non_comm_read {

                let mut tmp_node;
                let mut node_ref = node_self;
                // run over all possible commutative writes & update the deps & dependent_txs structs for them
                loop {
                    {
                        let node = node_ref.read();
                        if node.data.tx_block_id == node_other_tx_id { 
                            break; 
                        }
                        tmp_node = Arc::clone(&node.next.as_ref().unwrap());

                        // if it is a write, and comes after the last non commutative, then it can only be commutative write
                        if node.data.is_write() {
                            // println!("Dependency between schedules: {:?} depends on {:?}", node.data.tx_block_id, node_other_tx_id);
                            let node_self_normalized_idx = node.data.tx_block_id - self.starting_tx_id;
                            self.deps[node_other_normalized_idx].get_or_insert(HashSet::new()).insert(node.data.tx_block_id);
                            self.dependent_txs[node_self_normalized_idx].get_or_insert(HashSet::new()).insert(node_other_tx_id);
                        }
                    }
                    node_ref = tmp_node;
                }
            }

            // if is first operation of some tx from 'other' schedule, then remove it the 'other's from partial_ready_queue &
            // add it to the partial ready of the tx from the 'self' schedule  
            if node_other_is_first_operation {
                other.execution_queues.remove_id_from_partial_ready(node_other_tx_id);
                self.partial_ready_tx[node_self_normalized_idx].get_or_insert(HashSet::new()).insert(node_other_tx_id);
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
    /// 
    /// This method may be called only to update dependencies on the structs, and not the depency field itself. This is useful
    /// when we need to run from the last non comm write over all commutative writes in between - we don't want to set the dependency field
    fn set_node_dependency(&mut self, dependent_node: &mut DependencyNode<VecOperation>, dependency_node: Option<NodeRef<VecOperation>>, 
        tid: TxId, first_operation: bool, set_dependency_field: bool) {
        #[cfg(feature = "exec_time")]
        self.start_node_dependency_timer();
        
        match dependency_node {
            Some(write) => {
                
                // set new operation's dependency on previous write
                if set_dependency_field {
                    dependent_node.set_dependency(Some(Arc::clone(&write)));
                }
                

                let last_write_op = write.read();
                let last_write_tx_id = last_write_op.data.tx_block_id; 
                let last_write_is_from_this_tx =  last_write_op.data.is_from_tx(tid);
                drop(last_write_op);

                let normalized_idx = self.tx_id_to_index(tid);
                let normalized_last_write = self.tx_id_to_index(last_write_tx_id);

                // Last write was made by another tx
                if !last_write_is_from_this_tx {
                    // set our tid as a dependent tx of the tx responsible for the write we need to wait for
                    self.dependent_txs[normalized_last_write].get_or_insert(HashSet::new()).insert(tid);

                    if first_operation {
                        self.partial_ready_tx[normalized_last_write].get_or_insert(HashSet::new()).insert(tid);
                    }

                    // Increase dependency count
                    self.deps[normalized_idx].get_or_insert(HashSet::new()).insert(last_write_tx_id);
                }
            },
            // No previous write
            None => {
                if first_operation {
                    self.execution_queues.push_partial_ready(tid);
                }
            }
        }

        #[cfg(feature = "exec_time")]
        self.stop_node_dependency_timer();
    }


    pub fn insert_untracked_operation(&mut self, sc_address: &ScAddr, key: &Vec<u8>, operation_node: NodeRef<VecOperation>) {
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
        
        if self.deps[tx_id - self.starting_tx_id].is_none() {
            // If tx has no dependencies, push to ready queue
            self.execution_queues.push_ready(tx_id);
        }
    }

    /// Appends a read operation at the end of the schedule
    /// 
    /// Sets the dependencies for this new read operation. This will depend on some factors:
    /// 
    /// - If Read is Commutative -> then can either depend on a previous NonComm Write, or on storage.
    /// - If Read is Non Commutativ -> then it depends on the most recent write (be it commutative or non commutative), or on storage.
    fn update_schedule_on_read_operation(&mut self, first_operation: bool, tx_id: TxId, 
        contract: &ScAddr, key_bytes: &Vec<u8>, commutativity: Commutativity) -> NodeRef<VecOperation> {

        #[cfg(feature = "exec_time")]
        self.start_node_creation_timer();

        // create a new operation node
        let operation = Operation::new(OpType::Read, tx_id, commutativity, first_operation);
        let mut op_node = DependencyNode::new(operation);

        // create empty schedule for this SC
        self.schedule.create_if_not_exists(contract);

        let LastWrites { commutative, non_commutative  } = self.schedule.get_last_writes(&contract, &key_bytes);

        #[cfg(feature = "exec_time")]
        self.stop_node_creation_timer();

        match commutativity {
            // If read is commutative -> depend on storage
            Commutativity::Commutative => {
                // println!("Commutative Read from {:?} depending on: {:?}", tx_id, non_commutative);
                self.set_node_dependency(&mut op_node, None, tx_id, first_operation, true);
            },
            Commutativity::NonCommutative => { // run over all commwrites in between & mark all as dependencies
                let mut tmp_node;
                let mut last_write_is_from_different_tx = false;

                // fetch the first dependency -> Mya be either th elast non comm write, OR the head of the linked list.
                // We still have to check if that node is from a different transaction though!
                let node_ref = if let Some(last_non_comm_write) = non_commutative.as_ref() {
                    last_write_is_from_different_tx = last_non_comm_write.read().data.tx_block_id != tx_id;
                    Some(Arc::clone(last_non_comm_write))
                } else if let Some(head) = self.schedule.get_operations_list_head(contract, key_bytes.as_slice()) {
                    //  we may not have a starting node, thus the if let below wrapping the loop
                    last_write_is_from_different_tx = head.read().data.tx_block_id != tx_id;
                    Some(head)
                } else { None };
                
                if let Some(mut node_ref) = node_ref {
                    if last_write_is_from_different_tx {
                        loop {
                            {
                                let node = node_ref.read();
                                let node_has_no_next = node.next.is_none();
                                let node_id = node.data.tx_block_id;
                                // if it is a write, and comes after the last non commutative, then it can only be commutative write (ignoring the starting node)
                                if node.data.is_write() {
                                    drop(node);
                                    self.set_node_dependency(&mut op_node, Some(Arc::clone(&node_ref)), tx_id, first_operation, false);
                                }
    
                                // we can only break after setting the dependency
                                if node_has_no_next { break; }
                                tmp_node = Arc::clone(&node_ref.read().next.as_ref().unwrap());
                            }
                            node_ref = tmp_node;
                        }
    
                        // If there is a previous non_comm write, then use that as the 'dependency' pointer. Else, don't set node dependencies - all dependencies have already been set
                        // by the above loop
                        if let Some(non_commutative) = non_commutative { 
                            self.set_node_dependency(&mut op_node, Some(non_commutative), tx_id, first_operation, true);
                        }
                    }
                } 
                // No dependencynode in the list of operations -> then will be pushed to partial_ready
                else {
                    self.set_node_dependency(&mut op_node, None, tx_id, first_operation, true);
                }
            }
        };

        let concurrent_op_node = Arc::new(RwLock::new(op_node));
        self.schedule.append(contract, key_bytes, Arc::clone(&concurrent_op_node), OpType::Read, commutativity);
        concurrent_op_node

    }

    fn update_schedule_on_write_operation(&mut self, first_operation: bool, tx_id: TxId, 
        contract: &ScAddr, key_bytes: &Vec<u8>, commutativity: Commutativity) -> NodeRef<VecOperation> {

        #[cfg(feature = "exec_time")]
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

        #[cfg(feature = "exec_time")]
        self.stop_node_creation_timer();

        concurrent_op_node
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use serial_test::serial;

    use crate::{
        symb_exec::{Commutativity, Key, StorageDependency, TxRWS}, testing::mock_tx_operation, vm_manager::{serial_schedule::ScheduleBuilder, vm_manager::VMTransaction}, vm_transactions::{ExecuteTx, TransactionEnum}, DependencyNode, InstantiatedEntryPoint, LastWrites, NodeRef, OpType, RWSContext, ReadWrite, ReplayLogs, SEStatus, ScAddr, Size, VecOperation};

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");
    const SC_ADDR_A: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
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


    #[test]
    #[serial]
    fn concurrent_schedule_build() {
        let mut concurrent_schedule = ScheduleBuilder::new();
        let mut block = vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &vec![1u8], 0, ReadWrite::write(), Commutativity::Commutative),
        ];

        concurrent_schedule.build_from_rws(&mut block);

        let deps = concurrent_schedule.deps;
        // tx_block_id should have 0 dependencies
        assert_eq!(deps[0].as_ref().unwrap().len(), 0);
        
        // pop only available tx - tx with id 1
        let mut ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.pop_front().unwrap(), 0);

        let mut partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
        assert!(partial_ready_q.pop_front().is_none());

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

        let tx1 = 0;
        let tx2 = 1;
        let tx3 = 2;
        let tx4 = 3;
        let tx5 = 4;
        let tx6 = 5;

        let mut concurrent_schedule = ScheduleBuilder::new();
        concurrent_schedule.build_from_rws(&mut vec![

            // Tx1: R(A), W(A), W(B), R(C), W(C)
            RWSContext {
                address: SC_ADDR_A.to_owned(),
                tx_message: Some(VMTransaction {
                    transaction: TransactionEnum::Execute(ExecuteTx {
                        contract_addr: SC_ADDR_A.to_owned(),
                        msg: br#""#.to_vec(),
                        hash: "".to_owned(),
                        sender: "".to_owned(),
                        funds: vec![],
                        reply: None,
                    }),
                    replay_logs: ReplayLogs::default(),
                }),
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
                address: SC_ADDR_A.to_owned(),
                tx_message: Some(VMTransaction {
                    transaction: TransactionEnum::Execute(ExecuteTx {
                        contract_addr: SC_ADDR_A.to_owned(),
                        msg: br#""#.to_vec(),
                        hash: "".to_owned(),
                        sender: "".to_owned(),
                        funds: vec![],
                        reply: None,
                    }),
                    replay_logs: ReplayLogs::default(),
                }),
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
                address: SC_ADDR_A.to_owned(),
                tx_message: Some(VMTransaction {
                    transaction: TransactionEnum::Execute(ExecuteTx {
                        contract_addr: SC_ADDR_A.to_owned(),
                        msg: br#""#.to_vec(),
                        hash: "".to_owned(),
                        sender: "".to_owned(),
                        funds: vec![],
                        reply: None,
                    }),
                    replay_logs: ReplayLogs::default(),
                }),
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
                address: SC_ADDR_A.to_owned(),
                tx_message: Some(VMTransaction {
                    transaction: TransactionEnum::Execute(ExecuteTx {
                        contract_addr: SC_ADDR_A.to_owned(),
                        msg: br#""#.to_vec(),
                        hash: "".to_owned(),
                        sender: "".to_owned(),
                        funds: vec![],
                        reply: None,
                    }),
                    replay_logs: ReplayLogs::default(),
                }),
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
                address: SC_ADDR_A.to_owned(),
                tx_message: Some(VMTransaction {
                    transaction: TransactionEnum::Execute(ExecuteTx {
                        contract_addr: SC_ADDR_A.to_owned(),
                        msg: br#""#.to_vec(),
                        hash: "".to_owned(),
                        sender: "".to_owned(),
                        funds: vec![],
                        reply: None,
                    }),
                    replay_logs: ReplayLogs::default(),
                }),
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
                address: SC_ADDR_A.to_owned(),
                tx_message: Some(VMTransaction {
                    transaction: TransactionEnum::Execute(ExecuteTx {
                        contract_addr: SC_ADDR_A.to_owned(),
                        msg: br#""#.to_vec(),
                        hash: "".to_owned(),
                        sender: "".to_owned(),
                        funds: vec![],
                        reply: None,
                    }),
                    replay_logs: ReplayLogs::default(),
                }),
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
        let mut ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.pop_front().unwrap(), tx1);
        assert_eq!(ready_q.pop_front().unwrap(), tx6);

        // PARTIAL_READY: { Tx2 }
        let mut partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
        assert_eq!(partial_ready_q.pop_front().unwrap(), tx2);


        let dependent_txs = concurrent_schedule.dependent_txs;
        // Tx2 & Tx4 depend on Tx1
        assert!(dependent_txs[tx1].as_ref().unwrap().contains(&tx2));
        assert!(dependent_txs[tx1].as_ref().unwrap().contains(&tx4));
        // Tx3 & Tx5 depend on Tx2
        assert!(dependent_txs[tx2].as_ref().unwrap().contains(&tx3));
        assert!(dependent_txs[tx2].as_ref().unwrap().contains(&tx5));
        // Tx3-6 have no dependencies
        assert!(dependent_txs[tx3].is_none());
        assert!(dependent_txs[tx4].is_none());
        assert!(dependent_txs[tx5].is_none());
        assert!(dependent_txs[tx6].is_none());

        let ready_partials = concurrent_schedule.partial_ready_tx;
        // Tx1 has T4 as ready partial
        assert!(ready_partials[tx1].as_ref().unwrap().contains(&tx4));
        // Tx2 has Tx3 & Tx5 as ready_partial
        assert!(ready_partials[tx2].as_ref().unwrap().contains(&tx3));
        assert!(ready_partials[tx2].as_ref().unwrap().contains(&tx5));
    }

    #[test]
    #[serial]
    fn untracked_write_no_dependencies() {
        let sc_address = SC_ADDR_A.to_owned();
        let key = vec![1u8];

        let mut concurrent_schedule = ScheduleBuilder::new();
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(sc_address.clone(), &vec![2u8], 0, ReadWrite::write(), Commutativity::NonCommutative),
        ]);
        
        // insert untracked write
        let op_node = DependencyNode::new_ref(OpType::Write, 0, Commutativity::NonCommutative, true);
        concurrent_schedule.insert_untracked_operation(&sc_address, &key, Arc::clone(&op_node));

        // tx1 has no dependencies
        let deps = concurrent_schedule.deps;
        assert_eq!(deps[0].as_ref().unwrap().len(), 0);

        // added to ready queue
        let mut ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.pop_front().unwrap(), 0);

        // not added to partial_ready
        let mut partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
        assert!(partial_ready_q.pop_front().is_none());

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
        let sc_address = SC_ADDR_A.to_owned();
        let key = vec![1u8];

        let mut concurrent_schedule = ScheduleBuilder::new();
        
        // random read write just for the txs to have at least 1 read/write
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &vec![2u8], 0, ReadWrite::write(), Commutativity::NonCommutative),
        ]);
        
        // insert untracked write
        let op_node_write = DependencyNode::new_ref(OpType::Write, 0, Commutativity::NonCommutative, true);
        concurrent_schedule.insert_untracked_operation(&sc_address, &key, Arc::clone(&op_node_write));

        // insert untracked read
        let op_node_read = DependencyNode::new_ref(OpType::Read, 0, Commutativity::NonCommutative, false);
        concurrent_schedule.insert_untracked_operation(&sc_address, &key, Arc::clone(&op_node_read));

        // tx has no dependencies
        let deps = concurrent_schedule.deps;
        assert_eq!(deps[0].as_ref().unwrap().len(), 0);

        // tx is in ready queue
        let mut ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.pop_front().unwrap(), 0);

        // tx is not in partial_ready
        let mut partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
        assert!(partial_ready_q.pop_front().is_none());

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
        let sc_address = SC_ADDR_A.to_owned();
        let key = vec![1u8];

        let mut concurrent_schedule = ScheduleBuilder::new();

        // each tx must have at least 1 RW - inside the schedule we pre-allocate a vector with the size of 
        // the number of different txs - and we only count txs by their RWS
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &vec![2u8], 0, ReadWrite::write(), Commutativity::NonCommutative),
            mock_tx_operation(SC_ADDR_A.to_owned(), &vec![3u8], 1, ReadWrite::read(),  Commutativity::NonCommutative),
        ]);
        
        // insert untracked write
        let op_node_write = DependencyNode::new_ref(OpType::Write, 0, Commutativity::NonCommutative, true);
        concurrent_schedule.insert_untracked_operation(&sc_address, &key, Arc::clone(&op_node_write));

        // insert untracked read
        let op_node_read = DependencyNode::new_ref(OpType::Read, 1, Commutativity::NonCommutative, true);
        concurrent_schedule.insert_untracked_operation(&sc_address, &key, Arc::clone(&op_node_read));

        // tx1 has no dependencies
        let deps = concurrent_schedule.deps;
        assert_eq!(deps[0].as_ref().unwrap().len(), 0);

        // tx2 has no dependencies - recall we are simulating running time - an untracked operations is only 'tracked' when the tx is
        // executing. And if it started executing, is beacause it was either in READY or PARTIAL_READY queue, so it had no dependencies.
        // Even if it now depends on tx1, the operation itself will need to wait on tx1's operation, but still, tx2 is not marked
        // to have any dependencies since it already started executing.
        assert_eq!(deps[1].as_ref().unwrap().len(), 0);

        // here we are checking only on the original RWS - the tx placement in the queues does not count for untracked RWS
        // tx1 is in ready queue
        let mut ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.pop_front().unwrap(), 0);
        // tx2 is in ready queue
        assert_eq!(ready_q.pop_front().unwrap(), 1);

        // tx1 nor tx2 are in partial_ready
        let mut partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
        assert!(partial_ready_q.pop_front().is_none());

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
}