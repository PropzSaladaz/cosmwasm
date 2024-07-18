use std::{
    collections::{HashMap, HashSet, VecDeque}, fmt, io::{self, Write}, sync::{atomic::{AtomicUsize, Ordering}, Arc, RwLock}, thread
};

use parking_lot::{Mutex, Condvar};

use dashmap::DashMap;

use crate::{symb_exec::{Commutativity, Key, ReadWrite}, testing::ConcurrentStorage, BackendApi, Querier, SCManager, VMMessage};

use super::vm_manager::RWSContext;

#[cfg(feature = "debug_graph")]
use super::dot_schedule::{DotSchedule, NodeColor};

// size of a smart contract address
pub const ADDR_SIZE: usize = 32; 

pub type ScAddr = [u8; ADDR_SIZE];
pub type TxId = usize;

#[derive(Debug)]
pub struct QueueSignal {
    // the TxId represents the number of notifications made, aka
    // number of txs pushed to the queues
    lock: Mutex<bool>,
    cvar: Condvar,
}

impl PartialEq for QueueSignal {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl QueueSignal {
    fn new() -> QueueSignal {
        QueueSignal {
            lock: Mutex::new(false),
            cvar: Condvar::new(),
        }
    }

    pub fn wait(&self) {
        let mut started = self.lock.lock();
        while !*started {
            self.cvar.wait(&mut started);
        }
        *started = false;
    }

    pub fn notify_one(&self) {
        let mut started = self.lock.lock();
        *started = true;
        self.cvar.notify_one();
    }

    pub fn notify_all(&self, txs_pushed: TxId) {
        let mut started = self.lock.lock();
        *started = true;
        self.cvar.notify_all();
    }
}

#[derive(Debug)]
pub struct OperationSignal {
    lock: Mutex<bool>,
    cvar: Condvar,
}

impl PartialEq for OperationSignal {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl OperationSignal {
    fn new() -> OperationSignal {
        OperationSignal {
            lock: Mutex::new(false),
            cvar: Condvar::new(),
        }
    }

    pub fn wait(&self) {
        let mut started = self.lock.lock();
        while !*started {
            self.cvar.wait(&mut started);
        }
        // we won't set 'started' to false - after an operation is complete,
        // all dependent txs will read from it. There is never the need 
        // for a tx to go back to waiting state after an operation is completed
    }

    pub fn notify_all(&self) {
        let mut started = self.lock.lock();
        *started = true;
        self.cvar.notify_all();
    }
}

#[derive(Debug, PartialEq)]
pub struct Operation {
    pub operation_type: OpType,
    pub commutativity: Commutativity,
    pub tx_block_id: TxId,
    pub value: Option<Vec<u8>>,
    pub signal: OperationSignal,
}


impl Operation {
    pub fn new(operation_type: OpType, tx_block_id: TxId, commutativity: Commutativity) -> Self {
        Self {
            operation_type,
            commutativity,
            tx_block_id,
            value: None,
            signal: OperationSignal::new(),
        }
    }

    pub fn set_value(&mut self, new_value: Vec<u8>) {
        self.value = Some(new_value);
        self.signal.notify_all();
    }

    pub fn wait_for_value(&self) -> Vec<u8> {
        if let Some(val) = &self.value {
            val.clone() // TODO - Optimization - should we return a clone???
        }
        else {
            self.signal.wait();
            self.value.as_ref().unwrap().clone()
        }
    }
}

// RwLock is needed since we may need to change the next field at runtime
pub type NodeRef<T> = Arc<RwLock<DependencyNode<T>>>;

/// Represents a node in the LinkedList
pub struct DependencyNode<T> {
    pub value: T,
    pub next: Option<NodeRef<T>>,
    pub prev: Option<NodeRef<T>>,
    pub dependency: Option<NodeRef<T>>
}

impl DependencyNode<Operation> {
    pub fn new_ref(operation_type: OpType, tx_block_id: TxId, commutativity: Commutativity) -> NodeRef<Operation> {
        Arc::new(RwLock::new(DependencyNode {
            value: Operation::new(operation_type, tx_block_id, commutativity),
            next: None,
            prev: None,
            dependency: None
        }))
    }
}

// Need to limit recursion. Else will result in stack overflow
impl<T: std::fmt::Debug> fmt::Debug for DependencyNode<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut debug_struct = f.debug_struct("DependencyNode");

        debug_struct.field("value", &self.value);

        if let Some(ref prev) = self.prev {
            let prev_value = &prev.read().unwrap().value;
            debug_struct.field("prev", prev_value);
        } else {
            debug_struct.field("prev", &None::<i32>);
        }

        if let Some(ref next) = self.next {
            let next_value = &next.read().unwrap().value;
            debug_struct.field("next", next_value);
        } else {
            debug_struct.field("next", &None::<i32>);
        }

        debug_struct.finish()
    }
}

impl PartialEq for DependencyNode<Operation> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && 
        match (&self.next, &other.next) {
            (Some(a), Some(b)) => {
                a.read().unwrap().value == b.read().unwrap().value
            },
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        } &&
        match (&self.prev, &other.prev) {
            (Some(a), Some(b)) => {
                a.read().unwrap().value == b.read().unwrap().value
            },
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        } &&
        match (&self.dependency, &other.dependency) {
            (Some(a), Some(b)) => {
                a.read().unwrap().value == b.read().unwrap().value
            },
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        }
    }
}

impl<T> DependencyNode<T> {
    fn new(value: T) -> Self {
        DependencyNode {
            value: value,
            next: None,
            prev: None,
            dependency: None,
        }
    }

    fn set_next(&mut self, operation_node: Option<NodeRef<T>>) {
        self.next = operation_node
    }


    fn set_prev(&mut self, operation_node: Option<NodeRef<T>>) {
        self.prev = operation_node
    }

    fn set_dependency(&mut self, operation_node: Option<NodeRef<T>>) {
        self.dependency = operation_node
    }

}

#[derive(Debug)]
pub struct LinkedList<T> {
    pub head: Arc<RwLock<NodeRef<T>>>,
    pub tail: Arc<RwLock<NodeRef<T>>>,
}

impl<T: std::fmt::Debug> LinkedList<T> {
    fn new(item: NodeRef<T>) -> Self {
        LinkedList {
            head: Arc::new(RwLock::new(Arc::clone(&item))),
            tail: Arc::new(RwLock::new(Arc::clone(&item))),
        }
    }

    fn append(&self, item: NodeRef<T>) { // TODO - maybe we should keep locks for the entirity of this method - may have concurrency issues
        // set item.prev = tail
        {
            let tail_lock = self.tail.read().unwrap();
            let tail_item = &(*tail_lock);
            let tail_item_ref = Arc::clone(tail_item);

            let mut item_lock = item.write().unwrap();
            item_lock.set_prev(Some(tail_item_ref));
        }
        

        // set tail.next = item
        {
            let mut tail_lock = self.tail.write().unwrap();
            {
                let mut tail_item_lock = tail_lock.write().unwrap();
                tail_item_lock.set_next(Some(Arc::clone(&item)));
            }
            
            // set new tail
            *tail_lock = item;
        }
    }

    /// Given 2 nodes: [I] and [R]
    /// This method inserts [I] to the left of [R] in the linked list:
    /// 
    /// BEFORE
    /// [L]->[R]
    /// 
    /// AFTER
    /// [L]->[I]->[R]
    fn insert_to_left_of(&self, item_to_insert: NodeRef<T>, item_to_right: NodeRef<T>) { // TODO - maybe we should keep locks for the entirity of this method - may have concurrency issues
        let mut item_right_lock = item_to_right.write().unwrap();
        // fetch [L] from [R], and set [L]'s next value to [I]
        let prev_of_item_right = &item_right_lock.prev;
        match prev_of_item_right {
            Some(prev) => prev.write().unwrap().set_next(Some(Arc::clone(&item_to_insert))),
            None => { // we are inserting to the left of head - need to update head
                let mut head = self.head.write().unwrap();
                *head = Arc::clone(&item_to_insert);
            },
        };

        // set [I]'s prev to [L], and [I]'s next to [R]
        {
            let mut node = item_to_insert.write().unwrap();
            node.set_prev(match prev_of_item_right {
                Some(prev) => Some(Arc::clone(prev)),
                None => None,
            });
            node.set_next(Some(Arc::clone(&item_to_right)));
        }

        // set [R]'s prev to [I]
        item_right_lock.set_prev(Some(item_to_insert));

    }

}

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum OpType {
    Read,
    Write,
}


pub type LinkedListRef = Arc<LinkedList<Operation>>;
pub type SCSchedule = DashMap<Vec<u8>, LinkedListRef>;

type LastWrite = Arc<RwLock<NodeRef<Operation>>>;

/// Represents a schedule for some execution block:
/// SC -> key -> Linked list of operations for that item & SC
#[derive(Debug)]
struct Schedule {

    /// Stores a schedule, which is map of linked lists, one for each different KEY.
    /// Each linked list stores the order of operations affecting that item
    schedule: DashMap<ScAddr, SCSchedule>,

    /// Stores the last non-commutative write operation for each item of each SC
    /// SC -> key -> Last Write operation
    last_non_commutative_write: DashMap<ScAddr, DashMap<Vec<u8>, LastWrite>>
    // ^^ TODO - We should have a last_write for each tx - then when inserting a new untracked operation
    // we could directly fetch the last non-commutative write for that tx instead of running over the
    // entire list searching for it.
}

impl Schedule {
    fn new() -> Self {
        Self {
            schedule: DashMap::new(),
            last_non_commutative_write: DashMap::new(),
        }
    }

    /// Sets the entries of the schedule & last_write (there will be 1 last_write for each key in a SC)
    /// for the chosen SC address
    fn create_if_not_exists(&mut self, sc_address: ScAddr) {
        self.schedule.entry(sc_address).or_insert(DashMap::new());
        self.last_non_commutative_write.entry(sc_address).or_insert(DashMap::new());
    }

    pub fn get_last_non_commutative_write(&self, sc_address: ScAddr, key: &Vec<u8>) -> Option<NodeRef<Operation>> {
        match self.last_non_commutative_write.get(&sc_address).unwrap().get(key) {
            Some(last_write) => Some(Arc::clone(&last_write.read().unwrap())),
            None => None,
        }
    }

    /// Appends a new operation to the end of the list of the specified KEY in the specified SC.
    /// If the operation is write - updates last_write
    fn append(&mut self, sc_address: ScAddr, key: &Vec<u8>, operation_node: NodeRef<Operation>, op_type: OpType) {
        let sc_schedule = self.schedule.get(&sc_address).unwrap();
        
        // append node ref to linked list
        match sc_schedule.get(key) {
            Some(list) => list.append(Arc::clone(&operation_node)),
            None => {
                let new_linked_list = Arc::new(LinkedList::new(Arc::clone(&operation_node)));
                sc_schedule.insert(key.clone(), new_linked_list);
            },
        };
        self.update_last_non_commutative_write(sc_address, key, operation_node, op_type);

    }

    fn update_last_non_commutative_write(&self, sc_address: ScAddr, key: &Vec<u8>, operation_node: NodeRef<Operation>, op_type: OpType) {
        // Update last write
        match op_type {
            OpType::Read => (),
            OpType::Write => {
                let sc_last_write = self.last_non_commutative_write.entry(sc_address.clone()).or_insert(DashMap::new());
                let operation = sc_last_write.get(key); 
                match operation  {
                    Some(last_write) => {
                        let mut last_write = last_write.write().unwrap();
                        *last_write = Arc::clone(&operation_node);
                    },
                    None => {
                        let last_write = Arc::new(RwLock::new(Arc::clone(&operation_node)));
                        sc_last_write.insert(key.clone(), last_write);
                    },
                }
            }
        };
    }

    // TODO - We should store references in the DashMap for the sc_address & keys, not the values themselves. Else, we will need to clone the values each time...
    // TODO - We should keep track of the txs that depend on a tx A. Such that when a untracked operation appears,
    // we can fetch all txs depending on A, and now make them depend on the new tx (responsible for the new operation) if needed.

    /// Insert an untracked operation in the schedule. Start traversing from the tail of the linked list for the key & contract specified,
    /// Upon seing a tx with id < our tx_id that has a non-commutative write, we stop searching.
    /// We set our dependency on that write
    fn insert_untracked_operation(&self, sc_address: ScAddr, key: &Vec<u8>, tx_id: TxId, operation_node: NodeRef<Operation>, op_type: OpType) {
        let schedule = self.schedule.entry(sc_address).or_insert(DashMap::new());
        let linked_list = schedule.get(key) ;

        // if there is a linked-list (if there is any, then it must have at least 1 element by default)
        if let Some(linked_list) = linked_list {
            // TODO - Optimization!! We should store the last_non_commutative_write per each tx number
            // and we would only need to check if that last wrtie exists - then mark dependency on it. Else, 
            // read from storage
            let mut prev_node: Option<NodeRef<Operation>> = None;
            let mut node_ref = Arc::clone(&linked_list.tail.read().unwrap());
            let mut tmp_node;
            let mut highest_non_commutative_write: Option<NodeRef<Operation>> = None; 

            loop {
    
                {
                    let node = node_ref.read().unwrap();
                    // If the new operation is from the same tx, and the item we want to write/read to/from has operations from our tx,
                    // this new untracked operation will be inserted at the end of all previous operations from this tx.
                    // This has the side-effect of the next tx depending on this new RWS and not the last one!! This can produce wrong results!!
                    // the next operation from the next tx will start executing when this new operation we just inserted finished, and not the operation it previously depended on!!
                    // TODO - WE NEED TO INSERT IT IN THE EXACT SPOT!!

                    // The <= is because the current tx could have a non commutative write that must be read by any other tx
                    // comming after, including itself
                    if node.value.tx_block_id <= tx_id {
                        if Commutativity::NonCommutative == node.value.commutativity && 
                           OpType::Write == node.value.operation_type {
                            highest_non_commutative_write = Some(Arc::clone(&node_ref));
                            break;
                        }
                    }

                    // depends on state
                    if node.prev.is_none() { 
                        break; 
                    } 

                    tmp_node = Arc::clone(&node.prev.as_ref().unwrap());
                }
    
                prev_node = Some(Arc::clone(&node_ref));
                node_ref = tmp_node;
            }

            // Insert the node in the schedule
            if let Some(prev_node) = prev_node {
                linked_list.insert_to_left_of(Arc::clone(&operation_node), prev_node);
            }
            else {
                linked_list.append(Arc::clone(&operation_node));
            }

            // Update the dependencies of the node if it is a read
            if op_type == OpType::Read {
                // update dependency if operation is a Read, and we have a highest non commutative write
                if let Some(write) =  highest_non_commutative_write {
                    operation_node.write().unwrap().set_dependency(Some(write));
                }
            }
        }
        // no list of operations for the key -> create a brand new list
        else {
            schedule.insert(key.clone(), Arc::new(LinkedList::new(Arc::clone(&operation_node))));
        }

        // Independently of if the LinkedList already exsited or not, if it is a write, update last non commutative write
        if op_type == OpType::Write {
            // update last non commutative write
            self.update_last_non_commutative_write(sc_address, &key, operation_node, op_type);
        }



    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum TxState {
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

    /// Counter of number of txs executed. Used for termination condition
    executed: AtomicUsize,

    /// Total number of txs in the block
    total: TxId,

    /// Stores the number of dependencies for each tx
    deps: HashMap<TxId, AtomicUsize>,

    /// stores the txs that depend on some tx
    /// Tx -> Set of txs depending on it
    dependent_txs: DashMap<TxId, HashSet<TxId>>,

    /// stores the txs that have their 1st operation depending on it
    /// Tx -> Set of txs which their 1st operation depends on this tx
    partial_ready_tx: DashMap<TxId, HashSet<TxId>>,

    /// Signal used when any tx is pushed either to READY or PARTIAL_READY queue
    execution_queues: QueueSignal,

    // msg idx in the sequence of messages in current block
    pub ready_queue: Mutex<VecDeque<TxId>>,
    partial_ready_queue: Mutex<VecDeque<TxId>>,
    total_ready_txs: AtomicUsize,

    /// mapping of SC_address -> key -> linked list of operations
    schedule: Schedule,
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

impl ConcurrentSchedule {
    pub fn new() -> Self {
        ConcurrentSchedule {
            tx_states: vec![],
            executed: AtomicUsize::new(0),
            total: 0,

            transactions: HashSet::new(),

            deps: HashMap::new(),

            execution_queues: QueueSignal::new(),

            total_ready_txs: AtomicUsize::new(0),
            ready_queue: Mutex::new(VecDeque::new()),
            partial_ready_queue: Mutex::new(VecDeque::new()),
            
            schedule: Schedule::new(),
            
            dependent_txs: DashMap::new(),

            partial_ready_tx: DashMap::new(),
        }
    }

    /// Updates the execution state of a transaction.
    /// This is done without any locking mechanisms as txs are already synchronized
    /// via the READY and PARTIAL_READY queues.
    fn set_tx_status(&self, tx_id: TxId, tx_status: TxState) {
        if tx_id >= self.total { panic!("Tx id must be less than the total number of transactions") };
        let ptr = self.tx_states.as_ptr() as *mut TxState;
        unsafe { *ptr.offset(tx_id as isize) = tx_status }
    }


    pub fn increase_executed_count(&self) {
        self.executed.fetch_add(1, Ordering::SeqCst);
    }

    fn has_messages_to_execute(&self) -> bool {
        self.executed.load(Ordering::SeqCst) < self.total
    }

    /// Should be called when a tx/message is finished executing
    /// Runs over the dependencies on the tx_id (current tx that finished executing),
    /// and decreases the dependency count on each by 1.
    /// If any of those reaches dependency count of 0 & is not executing => push to READY_QUEUE.
    /// At the end, push all partial_ready into PARTIAL_READY_QUEUE
    /// If is an instantiation, also mark the instantiation dependency as complete.
    pub fn on_tx_finish(&self, context: &RWSContext) {
        let tx_id = context.tx_block_id;
        let mut added_txs = 0;
        // if tx has dependent txs
        if let Some(dependent_txs) = self.dependent_txs.get(&tx_id) {
            for dependent_tx in dependent_txs.iter() {
                let dependencies = self.deps.get(&dependent_tx).unwrap();
                dependencies.fetch_sub(1, Ordering::SeqCst);
    
                let tx_status = self.tx_states[*dependent_tx];
                if dependencies.load(Ordering::SeqCst) == 0 && (tx_status == TxState::NotExecuted) {

                    {
                        self.ready_queue.lock().push_back(*dependent_tx);
                    }
                    added_txs += 1;
                    
                    let mut current_tx_partials = self.partial_ready_tx.get_mut(&tx_id).unwrap();
                    (*current_tx_partials).remove(dependent_tx);
                }
            }
        }

        // if tx has tx_partials - push them to partial ready queue
        if let Some(current_tx_partials) = self.partial_ready_tx.get(&tx_id) {
            let mut partial_ready_lock = self.partial_ready_queue.lock();
            for tx in current_tx_partials.iter() {
                added_txs += 1;
                partial_ready_lock.push_back(*tx);
            }
        }

      
        self.set_tx_status(tx_id, TxState::Executed);

        self.increase_executed_count();

        self.increase_ready_txs_and_notify_threads(added_txs);
    }

    /// Notifies waiting threads if needed.
    /// 
    /// If no new txs added & no tx in queue, then notify all for checking termination condition.
    /// 
    /// If at least 1 new tx added:
    /// Current thread executing only notifies other waiting threads if it pushes at least 2 new txs.
    /// If it is only 1 tx, the current thread can itself handle it and avoid overhead of waking all
    /// the waiting threads
    fn increase_ready_txs_and_notify_threads(&self, added_txs: TxId) {
        if added_txs == 0 {
            let current_ready_txs = self.total_ready_txs.load(Ordering::SeqCst);
            if current_ready_txs == 0 {
                // println!("Notifying all: added_txs = {:?}", added_txs);
                self.execution_queues.notify_all(added_txs); 
            }
        }
        else {
            self.total_ready_txs.fetch_add(added_txs, Ordering::SeqCst);
            if added_txs > 2 {
                // println!("Notifying all: added_txs = {:?}", added_txs);
                self.execution_queues.notify_all(added_txs); 
            }
            else if added_txs == 2 {
                // println!("Notifying one: added_txs = {:?}", added_txs); 
                self.execution_queues.notify_one(); 
            }
            else {
                // println!("Not notifying any other thread - I can take care of it");
            }
        }
    }

    pub fn get_next_message_to_execute(&self) -> Option<TxId> {
        while self.has_messages_to_execute() {

            // try popping from ready
            if let Some(ready) = self.ready_queue.lock().pop_front() {
                self.set_tx_status(ready, TxState::Executing);
                // println!("Thread: {:?} fetched from READY_QUEUE", thread::current().id());
                io::stdout().flush().unwrap();
                return Some(ready)
            }
            // if ready is empty, try popping from partial_ready
            if let Some(partial_ready) = self.partial_ready_queue.lock().pop_front() {
                // println!("Thread: {:?} fetched from PARTIAL_READY_QUEUE", thread::current().id());
                io::stdout().flush().unwrap();
                self.set_tx_status(partial_ready, TxState::Executing);
                return Some(partial_ready)
            }

            // println!("Thread: {:?} waiting on new free tx", thread::current().id());
            // wait for at least one having one item
            self.execution_queues.wait();
            // panic!("SUII");
        }
        None
    }

    /// Builds an execution schedule from a sequence of RWS's per messages.
    /// This RWS will first be sorted to have all RWSs that do not depend on storage and are complete to come first,
    /// and only after comes all the RWSs that are either incomplete, or depend on storage.
    /// 
    /// Then run over each RWS & insert it in the schedule marking the dependencies between operations & transactions
    pub fn build_from_rws(&mut self, block: &mut Vec<RWSContext>) {

        self.total = block.len() as TxId;

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

            if self.deps.entry(tx_id).or_insert(AtomicUsize::new(0)).load(Ordering::SeqCst) == 0 { // no dependencies
                self.ready_queue.lock().push_back(tx_id);
                // no need to increment self.total_ready_txs as we already incremented it -
                // A ready tx must have been a partial ready first.
                // we are just moving it from the partial_ready queue to the ready_queue

                // println!("QUEUE: Notify one ");
                // self.execution_queues.notify_one(); //TEST

                // Remove it from partial_ready
                let mut idx = 0;
                let mut queue = self.partial_ready_queue.lock();
                for item in queue.iter() {
                    if *item == tx_id { break; }
                    idx += 1;
                }
                queue.remove(idx);
            }
            // println!("QUEUE: Notify one ");
            // self.execution_queues.notify_one(); // TEST


        }
    }

    pub fn insert_untracked_operation(&self, sc_address: ScAddr, key: &Vec<u8>, operation_node: NodeRef<Operation>) {
        let node_lock = operation_node.read().unwrap();
        let op_type = node_lock.value.operation_type;
        let tx_id = node_lock.value.tx_block_id;
        drop(node_lock);

        if !self.transactions.contains(&tx_id) { 
            panic!(
                "Trying to insert a Read/Write operation from an unseen transaction!.
            Every transaction should have at least one Read/Write operation detected by the Symb Exec engine at the start."
            );
        }

        self.schedule.insert_untracked_operation(sc_address, key, tx_id, operation_node, op_type);
        
        if let Some(dep) = self.deps.get(&tx_id) {
            if dep.load(Ordering::SeqCst) == 0 {
                // If tx has no dependencies, push to ready queue
                self.ready_queue.lock().push_back(tx_id);
                self.total_ready_txs.fetch_add(1, Ordering::SeqCst);
            }
        }

    }

    /// Appends a read operation at the end of the schedule
    fn update_schedule_on_read_operation(&mut self, first_operation: bool, tx_id: TxId, contract: ScAddr, key_bytes: &Vec<u8>, commutativity: Commutativity) -> NodeRef<Operation> {
        // create a new operation node
        let operation = Operation::new(OpType::Read, tx_id, commutativity);
        let mut op_node = DependencyNode::new(operation);

        // create empty schedule for this SC
        self.schedule.create_if_not_exists(contract);

        // Find last write operation
        match self.schedule.get_last_non_commutative_write(contract, &key_bytes) {
            Some(write) => {
                // set new operation's dependency on previous write
                op_node.set_dependency(Some(Arc::clone(&write)));

                let last_write_op = write.read().unwrap();
                let last_write_op = &last_write_op.value;

                // Last write was made by another tx
                if last_write_op.tx_block_id != tx_id {
                    // set our tid as a dependent tx of the tx responsible for the write we need to wait for
                    let mut dependent_txs = self.dependent_txs.entry(last_write_op.tx_block_id).or_insert(HashSet::new());
                    dependent_txs.insert(tx_id);

                    if first_operation {
                        let mut partial_ready = self.partial_ready_tx.entry(last_write_op.tx_block_id).or_insert(HashSet::new());
                        partial_ready.insert(tx_id); 
                    }

                    // // Increase dependency count
                    let tx_dependencies = self.deps.entry(tx_id).or_insert(AtomicUsize::new(0));
                    tx_dependencies.fetch_add(1, Ordering::SeqCst);

                }  // Else, if last write was done by our tx, just append it to schedule

            },
            // No previous write
            None => {
                if first_operation {
                    self.partial_ready_queue.lock().push_back(tx_id);
                    self.total_ready_txs.fetch_add(1, Ordering::SeqCst);
                }
            }
        };

        let concurrent_op_node = Arc::new(RwLock::new(op_node));
        self.schedule.append(contract, key_bytes, Arc::clone(&concurrent_op_node), OpType::Read);
        concurrent_op_node

    }

    fn update_schedule_on_write_operation(&mut self, first_operation: bool, tx_id: TxId, contract: ScAddr, key_bytes: &Vec<u8>, commutativity: Commutativity) -> NodeRef<Operation> {
        // create a new operation node
        let operation = Operation::new(OpType::Write, tx_id, commutativity);
        let op_node = DependencyNode::new(operation);

        // create empty schedule for this SC
        self.schedule.create_if_not_exists(contract);
        // append to schedule
        let concurrent_op_node = Arc::new(RwLock::new(op_node));
        self.schedule.append(contract, key_bytes, Arc::clone(&concurrent_op_node), OpType::Write);
        if first_operation {
            self.partial_ready_queue.lock().push_back(tx_id);
            self.total_ready_txs.fetch_add(1, Ordering::SeqCst);
        }
        concurrent_op_node
    }

    /// Given a state manager (a struct that keeps info about the state of each SC),
    /// It runs over all SC addresses & keys stored in the schedules, fetches the last non commutative write
    /// node of each & saves the value of that node to storage
    pub fn persist_schedule<A, S, Q>(&self, state_manager: &SCManager<A, S, Q>) 
    where
        A: BackendApi,
        S: ConcurrentStorage,
        Q: Querier
    {
        // run over each schedule of each SC
        for schedule in &*self {
            let sc_address = *schedule.key();

            // println!("Persist schedule: {:?}", sc_address);
            for i in state_manager.sc_storage.iter() {
                // println!("SC Manager stored contract address: {:?}", i.key());

                // println!("SC storage: {:#?}", i.value().state.storage);
            }
            let sc_storage = state_manager.get_contract_storage(sc_address);

            // run over all keys of each SC
            for operations_per_key in schedule.value() {
                let key = operations_per_key.key();

                // persist last write
                if let Some(last_non_commutative_write) = self.schedule.get_last_non_commutative_write(sc_address, key) {
                    let node_val = &last_non_commutative_write.read().unwrap().value.value;
                    let node_val = node_val.as_ref().expect("Persisting schedule: Last non commutative write should have its value set.");
                    // TODO - is the calculation of gas cost needed here ?? Where should we put it ?
                    sc_storage.set(key, node_val.as_slice()).0.unwrap();
                }
            }
        }
    }

    pub fn set_value(node: &NodeRef<Operation>, value: &[u8]) {
        let mut node = node.write().unwrap();
        (*node).value.value = Some(value.to_vec());
        (*node).value.signal.notify_all(); 
    } 

    #[cfg(feature = "debug_graph")]
    pub fn generate_debug_graph(&self, graph_name: String, rws:  &Vec<RWSContext>) {
        let mut dot = DotSchedule::new(NodeColor::LightBlue, 2);

        let dot_file = dot.parse(self, &rws);
        dot.save_as_png(dot_file, graph_name).unwrap();
    }

}


#[cfg(test)]
mod tests {
    use std::sync::{atomic::Ordering, Arc, RwLock};

    use crate::{
        symb_exec::{Commutativity, Key, ReadWrite, StorageDependency, TxRWS}, testing::{mock_persistent_backend, mock_tx_operation, 
            ConcurrentStorage, MockApi, MockConcurrentStorage, MockQuerier}, vm_manager::vm_manager::{InstantiatedEntryPoint, RWSContext, VMMessage}, wasm_backend::{compile, make_compiling_engine}, ConcurrentSchedule, SCManager, SEStatus, ScAddr, Size
    };

    use super::{DependencyNode, LinkedList, NodeRef, OpType, Operation, Schedule};

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");
    const SC_ADDR_A: ScAddr = *b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    
    const DEFAULT_MEMORY_LIMIT: Size = Size::mebi(64);

    fn assert_node_next(node: &NodeRef<Operation>, node_next: &NodeRef<Operation>) {
        let node = node.read().unwrap();
        let next = node.next.as_ref().unwrap().read().unwrap();

        let node_next = node_next.read().unwrap();

        assert_eq!(*next, *node_next);
    }

    fn assert_node_prev(node: &NodeRef<Operation>, node_prev: &NodeRef<Operation>) {
        let node = node.read().unwrap();
        let next = node.prev.as_ref().unwrap().read().unwrap();

        let node_prev = node_prev.read().unwrap();

        assert_eq!(*next, *node_prev);
    }

    fn assert_node_dependency(node: &NodeRef<Operation>, node_dep: &NodeRef<Operation>) {
        let node = node.read().unwrap();
        let next = node.dependency.as_ref().unwrap().read().unwrap();

        let node_dep = node_dep.read().unwrap();

        assert_eq!(*next, *node_dep);
    }

    fn mock_state_manager(sc_address: ScAddr) -> SCManager<MockApi, MockConcurrentStorage, MockQuerier> {
        // create a state manager
        let state_manager: SCManager<MockApi, MockConcurrentStorage, MockQuerier> = SCManager::new();
        state_manager.save_code(CONTRACT).unwrap();

        assert_eq!(state_manager.get_code(0).unwrap(), CONTRACT);
        
        // Create the compiled module & storage
        let code = state_manager.get_code(0).unwrap();
        let engine = make_compiling_engine(Some(DEFAULT_MEMORY_LIMIT));
        let module: wasmer::Module = compile( &engine, code.as_slice()).unwrap();
        let storage = Arc::new(MockConcurrentStorage::default());
        let backend = Arc::new(mock_persistent_backend(&[], storage));

        // save instance
        state_manager.save_instance(
            sc_address,
            0,
            Arc::new(module),
            backend);
        
        state_manager
    }

    #[test]
    fn linked_list_append() {
        let operation = Operation::new(OpType::Read, 1, Commutativity::NonCommutative);
        let node = Arc::new(RwLock::new(DependencyNode::new(operation)));
        let linked_list = LinkedList::new(Arc::clone(&node));

        assert_eq!(*linked_list.head.read().unwrap().read().unwrap(), *node.read().unwrap());
        assert_eq!(*linked_list.tail.read().unwrap().read().unwrap(), *node.read().unwrap());

        let operation2 = Operation::new(OpType::Write, 2, Commutativity::NonCommutative);
        let node2 = Arc::new(RwLock::new(DependencyNode::new(operation2)));
        linked_list.append(Arc::clone(&node2));

        assert_eq!(*linked_list.head.read().unwrap().read().unwrap(), *node.read().unwrap());
        assert_eq!(*linked_list.tail.read().unwrap().read().unwrap(), *node2.read().unwrap());

        assert_node_next(&node, &node2);
        assert_node_prev(&node2, &node);
    }

    #[test]
    fn linked_list_insert() {
        // setup linked list with 2 elements
        let operation = Operation::new(OpType::Read, 1, Commutativity::NonCommutative);
        let node = Arc::new(RwLock::new(DependencyNode::new(operation)));
        let linked_list = LinkedList::new(Arc::clone(&node));

        let operation2 = Operation::new(OpType::Write, 2, Commutativity::NonCommutative);
        let node2 = Arc::new(RwLock::new(DependencyNode::new(operation2)));
        linked_list.append(Arc::clone(&node2));

        // create new operation
        let operation3 = Operation::new(OpType::Write, 3, Commutativity::NonCommutative);
        let node3 = Arc::new(RwLock::new(DependencyNode::new(operation3)));

        linked_list.insert_to_left_of(Arc::clone(&node3), Arc::clone(&node));

        assert_eq!(*linked_list.head.read().unwrap().read().unwrap(), *node3.read().unwrap());
        assert_eq!(*linked_list.tail.read().unwrap().read().unwrap(), *node2.read().unwrap());

        assert_node_next(&node3, &node);
        assert_node_next(&node, &node2);

        assert_node_prev(&node, &node3);
        assert_node_prev(&node2, &node);

        // create new operation
        let operation4 = Operation::new(OpType::Write, 4, Commutativity::NonCommutative);
        let node4 = Arc::new(RwLock::new(DependencyNode::new(operation4)));

        linked_list.insert_to_left_of(Arc::clone(&node4), Arc::clone(&node2));

        assert_eq!(*linked_list.head.read().unwrap().read().unwrap(), *node3.read().unwrap());
        assert_eq!(*linked_list.tail.read().unwrap().read().unwrap(), *node2.read().unwrap());

        assert_node_next(&node3, &node);
        assert_node_next(&node, &node4);
        assert_node_next(&node4, &node2);

        assert_node_prev(&node, &node3);
        assert_node_prev(&node4, &node);
        assert_node_prev(&node2, &node4);
    }

    #[test]
    fn schedule_append() {
        let mut schedule = Schedule::new();
        let key_bytes = vec![1u8];

        schedule.create_if_not_exists(SC_ADDR_A);

        // create a read
        let operation = Operation::new(OpType::Read, 1, Commutativity::NonCommutative);
        let node = Arc::new(RwLock::new(DependencyNode::new(operation)));

        schedule.append(SC_ADDR_A, &key_bytes, Arc::clone(&node), OpType::Read);

        // 1 contract
        assert_eq!(schedule.schedule.len(), 1);
        {                                                                       // because of this mutable borrow :(
            // 1 key
            let created_contract_schedule = schedule.schedule.get(&SC_ADDR_A).unwrap();
            assert_eq!(created_contract_schedule.len(), 1);
        }

        // since we added a read, last_write should return None
        match schedule.get_last_non_commutative_write(SC_ADDR_A, &key_bytes) {
            Some(_) => assert!(false),
            None => assert!(true),
        }

        // create a write
        let operation2 = Operation::new(OpType::Write, 2, Commutativity::NonCommutative);
        let node2 = Arc::new(RwLock::new(DependencyNode::new(operation2)));

        schedule.append(SC_ADDR_A, &key_bytes, Arc::clone(&node2), OpType::Write);

        // 1 sc
        assert_eq!(schedule.schedule.len(), 1);
        // 1 key
        let created_contract_schedule = schedule.schedule.get(&SC_ADDR_A).unwrap();
        assert_eq!(created_contract_schedule.len(), 1);

        if let Some(node) = schedule.get_last_non_commutative_write(SC_ADDR_A, &key_bytes) {
            assert_eq!(*node.read().unwrap(), *node2.read().unwrap())
        }
        else { assert!(false) }

        // run over linked list
        let linked_list = created_contract_schedule.get(&key_bytes).unwrap();
        let node_head = Arc::clone(&*linked_list.head.read().unwrap());
        assert_eq!(*node_head.read().unwrap(), *node.read().unwrap());
        assert_eq!(*node_head.read().unwrap().next.as_ref().unwrap().read().unwrap(), *node2.read().unwrap());
    }

    #[test]
    fn concurrent_schedule_build() {
        let mut concurrent_schedule = ConcurrentSchedule::new();
        let mut block = vec![
            mock_tx_operation(SC_ADDR_A, &vec![1u8], 1, ReadWrite::write(), Commutativity::Commutative),
        ];

        concurrent_schedule.build_from_rws(&mut block);

        let deps = concurrent_schedule.deps;
        // tx_block_id should have 0 dependencies
        assert_eq!(deps.get(&1).unwrap().load(Ordering::SeqCst), 0);
        
        // pop only available tx - tx with id 1
        let ready_q = concurrent_schedule.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), 1);

        let partial_ready_q = concurrent_schedule.partial_ready_queue;
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
        assert_eq!(deps.get(&tx1).unwrap().load(Ordering::SeqCst), 0);
        assert_eq!(deps.get(&tx2).unwrap().load(Ordering::SeqCst), 1);
        assert_eq!(deps.get(&tx3).unwrap().load(Ordering::SeqCst), 1);
        assert_eq!(deps.get(&tx4).unwrap().load(Ordering::SeqCst), 1);
        assert_eq!(deps.get(&tx5).unwrap().load(Ordering::SeqCst), 1);
        assert_eq!(deps.get(&tx6).unwrap().load(Ordering::SeqCst), 0);
        
        // READY: { Tx1, Tx6 }
        let ready_q = concurrent_schedule.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), tx1);
        assert_eq!(ready_q.lock().pop_front().unwrap(), tx6);

        // PARTIAL_READY: { Tx2 }
        let partial_ready_q = concurrent_schedule.partial_ready_queue;
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

    #[test]
    fn untracked_write_no_dependencies() {
        let sc_address = SC_ADDR_A;
        let key = vec![1u8];

        let mut concurrent_schedule = ConcurrentSchedule::new();
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(sc_address, &vec![2u8], 1, ReadWrite::write(), Commutativity::NonCommutative),
        ]);
        
        // insert untracked write
        let op_node = DependencyNode::new_ref(OpType::Write, 1, Commutativity::NonCommutative);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node));

        // tx1 has no dependencies
        let deps = concurrent_schedule.deps;
        assert_eq!(deps.get(&1).unwrap().load(Ordering::SeqCst), 0);

        // added to ready queue
        let ready_q = concurrent_schedule.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), 1);

        // not added to partial_ready
        let partial_ready_q = concurrent_schedule.partial_ready_queue;
        assert!(partial_ready_q.lock().pop_front().is_none());

        // schedule head is the write node
        let sc_schedule = concurrent_schedule.schedule.schedule.get(&sc_address).unwrap();
        let head = &sc_schedule.get(&key).unwrap().head;
        assert_eq!(*head.read().unwrap().read().unwrap(), *op_node.read().unwrap());

        // schedule tail is the write node
        let tail = &sc_schedule.get(&key).unwrap().tail;
        assert_eq!(*tail.read().unwrap().read().unwrap(), *op_node.read().unwrap());

        // schedule last_non_commutative write is the write node
        let last_non_commutative_write = concurrent_schedule.schedule.get_last_non_commutative_write(sc_address, &key).unwrap();
        assert_eq!(*last_non_commutative_write.read().unwrap(), *op_node.read().unwrap());
    }

    #[test]
    fn untracked_read_with_dependency_on_write_same_tx() {
        let sc_address = SC_ADDR_A;
        let key = vec![1u8];

        let mut concurrent_schedule = ConcurrentSchedule::new();
        
        // random read write just for the txs to have at least 1 read/write
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(SC_ADDR_A, &vec![2u8], 1, ReadWrite::write(), Commutativity::NonCommutative),
        ]);
        
        // insert untracked write
        let op_node_write = DependencyNode::new_ref(OpType::Write, 1, Commutativity::NonCommutative);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node_write));

        // insert untracked read
        let op_node_read = DependencyNode::new_ref(OpType::Read, 1, Commutativity::NonCommutative);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node_read));

        // tx has no dependencies
        let deps = concurrent_schedule.deps;
        assert_eq!(deps.get(&1).unwrap().load(Ordering::SeqCst), 0);

        // tx is in ready queue
        let ready_q = concurrent_schedule.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), 1);

        // tx is not in partial_ready
        let partial_ready_q = concurrent_schedule.partial_ready_queue;
        assert!(partial_ready_q.lock().pop_front().is_none());

        // head is the 1st write operation
        let sc_schedule = concurrent_schedule.schedule.schedule.get(&sc_address).unwrap();
        let head = &sc_schedule.get(&key).unwrap().head;
        assert_eq!(*head.read().unwrap().read().unwrap(), *op_node_write.read().unwrap());

        // tail is the last read operation
        let tail = &sc_schedule.get(&key).unwrap().tail;
        assert_eq!(*tail.read().unwrap().read().unwrap(), *op_node_read.read().unwrap());

        // write operation's next value is the read operation
        assert_node_next(&op_node_write, &op_node_read);

        // read operation's prev value is the read operation
        assert_node_prev(&op_node_read, &op_node_write);

        // read operation's dependency should be set to the write node
        assert_node_dependency(&op_node_read, &op_node_write);

    }

    #[test]
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
        let op_node_write = DependencyNode::new_ref(OpType::Write, 1, Commutativity::NonCommutative);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node_write));

        // insert untracked read
        let op_node_read = DependencyNode::new_ref(OpType::Read, 2, Commutativity::NonCommutative);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node_read));

        // tx1 has no dependencies
        let deps = concurrent_schedule.deps;
        assert_eq!(deps.get(&1).unwrap().load(Ordering::SeqCst), 0);

        // tx2 has no dependencies - recall we are simulating running time - an untracked operations is only 'tracked' when the tx is
        // executing. And if it started executing, is beacause it was either in READY or PARTIAL_READY queue, so it had no dependencies.
        // Even if it now depends on tx1, the operation itself will need to wait on tx1's operation, but still, tx2 is not marked
        // to have any dependencies since it already started executing.
        assert_eq!(deps.get(&2).unwrap().load(Ordering::SeqCst), 0);

        // here we are checking only on the original RWS - the tx placement in the queues does not count for untracked RWS
        // tx1 is in ready queue
        let ready_q = concurrent_schedule.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), 1);
        // tx2 is in ready queue
        assert_eq!(ready_q.lock().pop_front().unwrap(), 2);

        // tx1 nor tx2 are in partial_ready
        let partial_ready_q = concurrent_schedule.partial_ready_queue;
        assert!(partial_ready_q.lock().pop_front().is_none());

        // head is the 1st write operation
        let sc_schedule = concurrent_schedule.schedule.schedule.get(&sc_address).unwrap();
        let head = &sc_schedule.get(&key).unwrap().head;
        assert_eq!(*head.read().unwrap().read().unwrap(), *op_node_write.read().unwrap());

        // tail is the last read operation
        let tail = &sc_schedule.get(&key).unwrap().tail;
        assert_eq!(*tail.read().unwrap().read().unwrap(), *op_node_read.read().unwrap());

        // write operation's next value is the read operation
        assert_node_next(&op_node_write, &op_node_read);

        // read operation's prev value is the read operation
        assert_node_prev(&op_node_read, &op_node_write);

        // read operation's dependency should be set to the write node
        assert_node_dependency(&op_node_read, &op_node_write);

    }

    #[test]
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
        let write_operation = linked_list.head.read().unwrap();

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
    fn on_tx_finish_no_dependencies_no_partials() {
        let sc_address = SC_ADDR_A;
        let key = vec![1u8];

        let mut concurrent_schedule = ConcurrentSchedule::new();
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(sc_address, &key, 1, ReadWrite::write(), Commutativity::NonCommutative),
        ]);
        
        // insert untracked write
        let op_node_write = DependencyNode::new_ref(OpType::Write, 1, Commutativity::NonCommutative);
        concurrent_schedule.insert_untracked_operation(sc_address, &key, Arc::clone(&op_node_write));
        
        concurrent_schedule.get_next_message_to_execute();
        concurrent_schedule.on_tx_finish(&RWSContext {
            rws: TxRWS {
                storage_dependency: StorageDependency::Independent,
                profile_status: SEStatus::Complete,
                rws: vec![],
            },
            address: SC_ADDR_A,
            tx_message: None,
            tx_block_id: 0
        });

        let deps = &concurrent_schedule.deps;
        assert_eq!(deps.get(&(1 as usize)).unwrap().load(Ordering::SeqCst), 0);
    }

}