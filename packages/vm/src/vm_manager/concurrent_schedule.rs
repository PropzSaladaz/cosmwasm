use std::{
    collections::{HashMap, HashSet, VecDeque}, fmt, i128, io::{self, Write}, sync::{atomic::{AtomicBool, AtomicUsize, Ordering}, Arc, RwLock}, thread
};

use parking_lot::{Mutex, Condvar};

use dashmap::DashMap;

use crate::{symb_exec::{Commutativity, Key, ReadWrite}, testing::{ConcurrentStorage, StorageWrapper}, BackendApi, Querier, SCManager, VMMessage};

use super::vm_manager::RWSContext;

#[cfg(feature = "debug_graph")]
use super::dot_schedule::{DotSchedule, NodeColor};

// size of a smart contract address
pub const ADDR_SIZE: usize = 32; 

pub type ScAddr = [u8; ADDR_SIZE];
pub type TxId = usize;

// TODO - we are currently assuming all will be signed integers.
// they may be unsigned - we need to create more conditions to conver to unsigned in cases of overflow of integer
// We may discard floats, as these are inherently non deterministic types
fn ascii_encoded_sub(lhs: &Vec<u8>, rhs: &Vec<u8>) -> Vec<u8> {
    let lhs = String::from_utf8(lhs.clone()).unwrap();
    let rhs = String::from_utf8(rhs.clone()).unwrap();

    let lhs = lhs.parse::<i128>().unwrap();
    let rhs = rhs.parse::<i128>().unwrap();

    let res = lhs - rhs;

    res.to_string().into_bytes()
}


fn ascii_encoded_add(lhs: &Vec<u8>, rhs: &Vec<u8>) -> Vec<u8> {
    let lhs = String::from_utf8(lhs.clone()).unwrap();
    let rhs = String::from_utf8(rhs.clone()).unwrap();

    let lhs = lhs.parse::<i128>().unwrap();
    let rhs = rhs.parse::<i128>().unwrap();

    let res = lhs + rhs;

    res.to_string().into_bytes()
}


#[derive(Debug)]
pub struct ConcurrentQueues {
    executed_txs: Mutex<TxId>,

    total_txs: TxId,

    ready_queue: Mutex<VecDeque<TxId>>,
    partial_ready_queue: Mutex<VecDeque<TxId>>,

    cvar: Condvar,
}

impl PartialEq for ConcurrentQueues {
    fn eq(&self, _other: &Self) -> bool {
        true
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
    /// Checks ready queue 1st, and if no elements available, checks prtial ready.
    /// Waits until signaled by another thread pushing a new element, or until no more txs
    /// to execute.
    fn pop(&self) -> Option<TxId> {
        
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
            let has_messages_to_execute = *lock < self.total_txs;
            while has_messages_to_execute {
                self.cvar.wait(&mut lock);
                continue 'try_popping;
            }
            // has no message to execute
            break 'try_popping;
        }

        // println!("Terminated");
        return None;
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


pub trait OperationValue: Clone + Sized {
    fn compute_delta(&self, old_val: &Self) -> Self;
    fn merge(&mut self, val: &Self);
}

impl OperationValue for Vec<u8> {
    fn compute_delta(&self, other: &Self) -> Self {
        ascii_encoded_sub(self, other)
    }

    fn merge(&mut self, other: &Self) {
        *self = ascii_encoded_add(self, other);
    }
}



#[derive(Debug, PartialEq)]
pub struct Operation<V: OperationValue> {
    pub operation_type: OpType,
    pub commutativity: Commutativity,
    pub tx_block_id: TxId,
    // in the future this can be made a generic parameter
    pub value: Option<V>,
    pub signal: OperationSignal,
}


impl<V: OperationValue> Operation<V> {
    pub fn new(operation_type: OpType, tx_block_id: TxId, commutativity: Commutativity) -> Self {
        Self {
            operation_type,
            commutativity,
            tx_block_id,
            value: None,
            signal: OperationSignal::new(),
        }
    }

    pub fn set_value(&mut self, new_value: V) {
        self.value = Some(new_value);
        self.signal.notify_all();
    }

    pub fn wait_for_value(&self) -> V {
        if let Some(val) = &self.value {
            val.clone() // TODO - Optimization - should we return a clone???
        }
        else {
            self.signal.wait();
            self.value.as_ref().unwrap().clone()
        }
    }

    pub fn is_read(&self) -> bool {
        return self.operation_type == OpType::Read;
    }

    pub fn is_write(&self) -> bool {
        return self.operation_type == OpType::Write;
    }

    pub fn is_commutative(&self) -> bool {
        return self.commutativity == Commutativity::Commutative;
    }

    pub fn is_from_tx(&self, tid: TxId) -> bool {
        return self.tx_block_id == tid;
    }
}

// RwLock is needed since we may need to change the next field at runtime
pub type NodeRef<T> = Arc<RwLock<DependencyNode<T>>>;
// we curently only support the data to be vec<u8>.
// To support other types we would need to have dynamic dispatch, and would
// require using Box<dyn OperationValue>, which adds a new level of indirection.
// Would be less efficient, but if needed, we can do it
pub type VecOperation = Operation<Vec<u8>>;

/// Represents a node in the LinkedList
pub struct DependencyNode<T> {
    pub data: T,
    pub next: Option<NodeRef<T>>,
    pub prev: Option<NodeRef<T>>,
    pub dependency: Option<NodeRef<T>>
}

impl DependencyNode<VecOperation> {
    pub fn new_ref(operation_type: OpType, tx_block_id: TxId, commutativity: Commutativity) -> NodeRef<VecOperation> {
        Arc::new(RwLock::new(DependencyNode {
            data: Operation::new(operation_type, tx_block_id, commutativity),
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

        debug_struct.field("value", &self.data);

        if let Some(ref prev) = self.prev {
            let prev_value = &prev.read().unwrap().data;
            debug_struct.field("prev", prev_value);
        } else {
            debug_struct.field("prev", &None::<i32>);
        }

        if let Some(ref next) = self.next {
            let next_value = &next.read().unwrap().data;
            debug_struct.field("next", next_value);
        } else {
            debug_struct.field("next", &None::<i32>);
        }

        debug_struct.finish()
    }
}

impl PartialEq for DependencyNode<VecOperation> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data && 
        match (&self.next, &other.next) {
            (Some(a), Some(b)) => {
                a.read().unwrap().data == b.read().unwrap().data
            },
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        } &&
        match (&self.prev, &other.prev) {
            (Some(a), Some(b)) => {
                a.read().unwrap().data == b.read().unwrap().data
            },
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        } &&
        match (&self.dependency, &other.dependency) {
            (Some(a), Some(b)) => {
                a.read().unwrap().data == b.read().unwrap().data
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
            data: value,
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


pub type LinkedListRef = Arc<LinkedList<VecOperation>>;
pub type SCSchedule = DashMap<Vec<u8>, LinkedListRef>;

type LastWrite = Arc<RwLock<NodeRef<VecOperation>>>;
type LastWriteMap =  DashMap<ScAddr, DashMap<Vec<u8>, LastWrite>>;


struct LastWrites {
    commutative: Option<NodeRef<VecOperation>>,
    non_commutative: Option<NodeRef<VecOperation>>
}

/// Represents a schedule for some execution block:
/// SC -> key -> Linked list of operations for that item & SC
#[derive(Debug)]
struct Schedule {

    /// Stores a schedule, which is map of linked lists, one for each different KEY.
    /// Each linked list stores the order of operations affecting that item
    schedule: DashMap<ScAddr, SCSchedule>,

    /// Stores the last non-commutative write operation for each item of each SC
    /// SC -> key -> Last Write operation
    last_non_commutative_write: LastWriteMap,
    last_commutative_write: LastWriteMap
    // ^^ TODO - We should have a last_write for each tx - then when inserting a new untracked operation
    // we could directly fetch the last non-commutative write for that tx instead of running over the
    // entire list searching for it.
}

impl Schedule {
    fn new() -> Self {
        Self {
            schedule: DashMap::new(),
            last_non_commutative_write: DashMap::new(),
            last_commutative_write: DashMap::new(),
        }
    }

    /// Returns the head node of a list of dependent operations on some Key of some Contract
    pub fn get_head_node(&self, address: &ScAddr, key: &[u8]) -> NodeRef<VecOperation> {
        let sc = self.schedule.get(address).unwrap();
        let list = sc.get(key).unwrap();
        let head_node = list.head.read().unwrap();
        Arc::clone(&head_node)
    }

    /// Sets the entries of the schedule & last_write (there will be 1 last_write for each key in a SC)
    /// for the chosen SC address
    fn create_if_not_exists(&mut self, sc_address: ScAddr) {
        self.schedule.entry(sc_address).or_insert(DashMap::new());
        self.last_non_commutative_write.entry(sc_address).or_insert(DashMap::new());
    }

    /// Return at most 2 writes - One Commutative and one Non COmmutative that represent the latest writes of each type
    /// for some SC and some key.
    /// 
    /// Depending on the Read operation comming after each of those writes, we may want to mark a dependency either on
    /// the Commutative or the Non Commutative write.
    /// 
    /// If the Read is Comm -> Mark dependency on the latest Non Commutative write
    /// If the read is Non COmmutative -> Mark dependency on the latest of both (can be wither Comm or NonCOmm write)
    pub fn get_last_writes(&self, sc_address: ScAddr, key: &Vec<u8>) -> LastWrites {
        let non_commutative = match self.last_non_commutative_write.get(&sc_address) {
            Some(non_comm_writes) => match non_comm_writes.get(key) {
                Some(last_write) => Some(Arc::clone(&last_write.read().unwrap())),
                None => None,
            },
            None => None,
        };

        let commutative = match self.last_commutative_write.get(&sc_address) {
            Some(comm_writes) => match comm_writes.get(key) {
                Some(last_write) => Some(Arc::clone(&last_write.read().unwrap())),
                None => None,
            },
            None => None,
        };

        LastWrites { commutative, non_commutative }
    }

    /// Appends a new operation to the end of the list of the specified KEY in the specified SC.
    /// If the operation is write - updates last_write
    fn append(&mut self, sc_address: ScAddr, key: &Vec<u8>, operation_node: NodeRef<VecOperation>, op_type: OpType) {
        let sc_schedule = self.schedule.get(&sc_address).unwrap();
        
        // append node ref to linked list
        match sc_schedule.get(key) {
            Some(list) => list.append(Arc::clone(&operation_node)),
            None => {
                let new_linked_list = Arc::new(LinkedList::new(Arc::clone(&operation_node)));
                sc_schedule.insert(key.clone(), new_linked_list);
            },
        };
        self.update_last_write(sc_address, key, operation_node, op_type);
    }

    /// Given an operation node for some key in some Contract, check if it is a Write. 
    /// If it is, then:
    /// 
    /// - If Commutative -> update the last commutative write tracker. THis is used by Non Commutative reads that may come after a commutative write.
    /// - If Non Commutative -> update the last non commutative tracker. This is used by either Commutative or Non Commutative reads that may come
    /// after a Non Commutative write.
    /// 
    /// The read operation coming after a write then needs to get the last write from both the Commutative and Non Commutative trackers & pick
    /// the node with the latest tx id (the most recent operation of those 2).
    fn update_last_write(&self, sc_address: ScAddr, key: &Vec<u8>, operation_node: NodeRef<VecOperation>, op_type: OpType) {

        // Aux function -> update a last write map (either the commutative or non commutative write map) with the new last write operation
        // clone the node with an Arc
        let set_write_if_not_exists = |last_write_tracker: &LastWriteMap, operation_node| {
            let sc_last_write = last_write_tracker.entry(sc_address.clone()).or_insert(DashMap::new());
            let operation = sc_last_write.get(key); 
            match operation  {
                Some(last_write) => {
                    let mut last_write = last_write.write().unwrap();
                    *last_write = Arc::clone(operation_node);
                },
                None => {
                    let last_write = Arc::new(RwLock::new(Arc::clone(operation_node)));
                    sc_last_write.insert(key.clone(), last_write);
                },
            }
        };

        match op_type {
            OpType::Read => (),
            OpType::Write => {
                let node_read_lock = operation_node.read().unwrap();
                if node_read_lock.data.is_commutative() {
                    set_write_if_not_exists(&self.last_commutative_write, &operation_node);
                }
                else {
                    set_write_if_not_exists(&self.last_non_commutative_write, &operation_node);
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
    fn insert_untracked_operation(&self, sc_address: ScAddr, key: &Vec<u8>, tx_id: TxId, operation_node: NodeRef<VecOperation>, op_type: OpType) {
        let schedule = self.schedule.entry(sc_address).or_insert(DashMap::new());
        let linked_list = schedule.get(key) ;

        // if there is a linked-list (if there is any, then it must have at least 1 element by default)
        if let Some(linked_list) = linked_list {
            // TODO - Optimization!! We should store the last_non_commutative_write per each tx number
            // and we would only need to check if that last wrtie exists - then mark dependency on it. Else, 
            // read from storage
            let mut prev_node: Option<NodeRef<VecOperation>> = None;
            let mut node_ref = Arc::clone(&linked_list.tail.read().unwrap());
            let mut tmp_node;
            let mut highest_non_commutative_write: Option<NodeRef<VecOperation>> = None; 

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
                    if node.data.tx_block_id <= tx_id {
                        if !node.data.is_commutative() && node.data.is_write() {
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
            self.update_last_write(sc_address, &key, operation_node, op_type);
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
    execution_queues: ConcurrentQueues,

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
            total: 0,

            transactions: HashSet::new(),

            deps: HashMap::new(),

            execution_queues: ConcurrentQueues::new(),
            
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
                let dependencies = self.deps.get(&dependent_tx).unwrap();
                dependencies.fetch_sub(1, Ordering::SeqCst);
    
                let tx_status = self.tx_states[*dependent_tx];
                if dependencies.load(Ordering::SeqCst) == 0 && (tx_status == TxState::NotExecuted) {

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

            if self.deps.entry(tx_id).or_insert(AtomicUsize::new(0)).load(Ordering::SeqCst) == 0 { // no dependencies
                self.execution_queues.push_ready(tx_id);
                self.execution_queues.remove_partial_ready(tx_id);
            }
        }
    }

    pub fn insert_untracked_operation(&self, sc_address: ScAddr, key: &Vec<u8>, operation_node: NodeRef<VecOperation>) {
        let node_lock = operation_node.read().unwrap();
        let op_type = node_lock.data.operation_type;
        let tx_id = node_lock.data.tx_block_id;
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
                self.execution_queues.push_ready(tx_id);
            }
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

                let last_write_op = write.read().unwrap();
                let last_write_tx_id = last_write_op.data.tx_block_id; 

                // Last write was made by another tx
                if !last_write_op.data.is_from_tx(tid) {
                    // set our tid as a dependent tx of the tx responsible for the write we need to wait for
                    let mut dependent_txs = self.dependent_txs.entry(last_write_tx_id).or_insert(HashSet::new());
                    dependent_txs.insert(tid);

                    if first_operation {
                        let mut partial_ready = self.partial_ready_tx.entry(last_write_tx_id).or_insert(HashSet::new());
                        partial_ready.insert(tid); 
                    }

                    // Increase dependency count
                    let tx_dependencies = self.deps.entry(tid).or_insert(AtomicUsize::new(0));
                    tx_dependencies.fetch_add(1, Ordering::SeqCst);
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
        let operation = Operation::new(OpType::Read, tx_id, commutativity);
        let mut op_node = DependencyNode::new(operation);

        // create empty schedule for this SC
        self.schedule.create_if_not_exists(contract);

        let LastWrites { commutative, non_commutative  } = self.schedule.get_last_writes(contract, &key_bytes);

        match commutativity {
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
                        let comm_id = comm.read().unwrap().data.tx_block_id;
                        let non_comm_id = non_comm.read().unwrap().data.tx_block_id;

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
        self.schedule.append(contract, key_bytes, Arc::clone(&concurrent_op_node), OpType::Read);
        concurrent_op_node

    }

    fn update_schedule_on_write_operation(&mut self, first_operation: bool, tx_id: TxId, 
        contract: ScAddr, key_bytes: &Vec<u8>, commutativity: Commutativity) -> NodeRef<VecOperation> {
        // create a new operation node
        let operation = Operation::new(OpType::Write, tx_id, commutativity);
        let op_node = DependencyNode::new(operation);

        // create empty schedule for this SC
        self.schedule.create_if_not_exists(contract);
        // append to schedule
        let concurrent_op_node = Arc::new(RwLock::new(op_node));
        self.schedule.append(contract, key_bytes, Arc::clone(&concurrent_op_node), OpType::Write);
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
                let LastWrites { commutative, non_commutative } = self.schedule.get_last_writes(sc_address, key);

                // persist last write - If it is commutative, then merge the deltas
                match (commutative, non_commutative) {
                    (Some(comm), Some(non_comm)) => {
                        let comm_id = comm.read().unwrap().data.tx_block_id;
                        let non_comm_id = non_comm.read().unwrap().data.tx_block_id;

                        if comm_id > non_comm_id { 
                            let node_val = self.merge_commutative_chain(&comm, &sc_storage, key);
                            sc_storage.set(key, node_val.as_slice()).0.unwrap();
                        }
                        else {
                            let node_val = &non_comm.read().unwrap().data.value;
                            let node_val = node_val.as_ref().expect("Persisting schedule: Last non commutative write should have its value set.");
                            sc_storage.set(key, node_val.as_slice()).0.unwrap();
                        }
                    },
                    
                    (Some(comm), None) => {
                        let node_val = self.merge_commutative_chain(&comm, &sc_storage, key);
                        sc_storage.set(key, node_val.as_slice()).0.unwrap();
                    },

                    (None, Some(non_comm)) => {
                        let node_val = &non_comm.read().unwrap().data.value;
                        let node_val = node_val.as_ref().expect("Persisting schedule: Last non commutative write should have its value set.");
                        sc_storage.set(key, node_val.as_slice()).0.unwrap();
                    },
                    (None, None) => ()
                }
            }
        }
    }

    /// Searches for the previous commutative read associated to the passed commutative write node
    fn get_prev_incr_read(node: &NodeRef<VecOperation>) -> NodeRef<VecOperation> {
        let node_read_lock = node.read().unwrap();
        let tx_id = node_read_lock.data.tx_block_id;
        let mut previous_op = Arc::clone(node_read_lock.prev.as_ref().unwrap());

        return loop {
            let node_lock = previous_op.read().unwrap();

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
        let node_read_lock = node.read().unwrap();
        let op_type = node_read_lock.data.operation_type;
        let commutativity = node_read_lock.data.commutativity;
        drop(node_read_lock);

        match op_type {
            OpType::Read => {
                match commutativity {
                    Commutativity::Commutative => {
                        let mut node = node.write().unwrap();
                        node.data.set_value(value.to_vec());
                    },
                    Commutativity::NonCommutative => {} // no need to write the read value to the node
                }
            },
             OpType::Write => {
                match commutativity {
                    Commutativity::Commutative => {
                        let prev_incr_read = ConcurrentSchedule::get_prev_incr_read(node);
                        let prev_incr_read_val = prev_incr_read.read().unwrap().data.value.as_ref().unwrap().clone();
                        let val = value.to_vec();
                        let delta = val.compute_delta(&prev_incr_read_val);

                        let mut node_write_lock = node.write().unwrap();
                        node_write_lock.data.set_value(delta);

                    },
                    Commutativity::NonCommutative => {
                        let mut node = node.write().unwrap();
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

        let mut merge_accumulated_delta = |delta: Vec<u8>| {
            if accumulated_deltas.is_empty() {
                accumulated_deltas = delta;
            }
            else {
                // println!("Accumulated deltas before: {:?}", accumulated_deltas);
                // println!("Value to add: {:?}", delta);
                accumulated_deltas.merge(&delta);
                // println!("Accumulated deltas after: {:?}", accumulated_deltas);
            }
        };

        loop {
            let node_lock = starting_node.read().unwrap();
            
            // println!("Node OpType: {:?}", node_lock.data.operation_type);
            // println!("Node Commutativity {:?}", node_lock.data.commutativity);

            // Commutative writes -> merge deltas
            if node_lock.data.is_write() {
                let value = node_lock.data.wait_for_value();
                // println!("Value from node: {:?}", value);
                merge_accumulated_delta(value);

                // This is a sufficient condition to stop. The first NonCommutative Write (of any tx tx) after a chain of 
                // commutative operations will always be the 'barrier' of all subsequent commutative operations.
                // They will always depend on this write.
                if !node_lock.data.is_commutative() {
                    // println!("Breaking out");
                    break accumulated_deltas;
                }
            }

            // Current node has a previous node
            if let Some(prev)  = &node_lock.prev {
                // println!("Going left");
                let tmp = Arc::clone(prev);

                drop(node_lock); // since node_lock borrows from previous_op. Needed for below assignment 
                starting_node = tmp;
            } 
            else { // We reached the head without finding any non commutative write -> merge deltas to storage value
                // println!("No Comm Write found");
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
        let node_read_lock = read_node.read().unwrap();

        if node_read_lock.data.is_read() {
            if node_read_lock.data.is_commutative() {

                let dependency_val = if let Some(dependency) = &node_read_lock.dependency {
                    let node_lock = dependency.read().unwrap();
                    // println!("Comm Read depnded on: {:?}", node_lock.data);
                    Some(node_lock.data.wait_for_value())
                }
                else {
                    concurrent_storage.get_uncharged(key)
                };

                let val: Vec<u8> = dependency_val.as_ref().unwrap().clone();
                drop(node_read_lock);

                read_node.write().unwrap().data.set_value(val);
                // println!("Commutative read value: {:?}", dependency_val);
                dependency_val
            }
            else {
                if let Some(dependency) = &node_read_lock.dependency {
                    // println!("Node has dependencies");
                    let node_lock = dependency.read().unwrap(); 

                    if node_lock.data.is_commutative() {
                        // println!("Merging commutative chain");
                        drop(node_lock);

                        let merged_deltas = self.merge_commutative_chain(dependency, concurrent_storage, key);
                        // println!("Merged Val: {:?}", merged_deltas);
                        Some(merged_deltas)
                    }
                    else {
                        // println!("Res: {:?}", node_lock.data.wait_for_value());
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
    use std::sync::{atomic::Ordering, Arc, RwLock};

    use parking_lot::lock_api::Mutex;
    use wasmer::Store;

    use crate::{
        internals::instance_from_module, 
        symb_exec::{Commutativity, Key, ReadWrite, StorageDependency, TxRWS}, 
        testing::{
            mock_concurrent_backend, mock_persistent_backend, mock_tx_operation, 
            ConcurrentStorage, MockApi, MockConcurrentStorage, MockQuerier, MockStorageWrapper
        }, 
        vm_manager::{
            concurrent_schedule::{ascii_encoded_add, ascii_encoded_sub, LastWrite, LastWrites}, 
            vm_manager::{InstantiatedEntryPoint, RWSContext, VMMessage}
        }, 
        wasm_backend::{compile, make_compiling_engine}, 
        ConcurrentSchedule, InstanceOptions, SCManager, SEStatus, ScAddr, Size
    };

    use super::{DependencyNode, LinkedList, NodeRef, OpType, Operation, Schedule, VecOperation};

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");
    const SC_ADDR_A: ScAddr = *b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const HIGH_GAS_LIMIT: u64 = 20_000_000_000_000; // ~20s, allows many calls on one instance
    const DEFAULT_MEMORY_LIMIT: Size = Size::mebi(64);

    fn assert_node_next(node: &NodeRef<VecOperation>, node_next: &NodeRef<VecOperation>) {
        let node = node.read().unwrap();
        let next = node.next.as_ref().unwrap().read().unwrap();

        let node_next = node_next.read().unwrap();

        assert_eq!(*next, *node_next);
    }

    fn assert_node_prev(node: &NodeRef<VecOperation>, node_prev: &NodeRef<VecOperation>) {
        let node = node.read().unwrap();
        let next = node.prev.as_ref().unwrap().read().unwrap();

        let node_prev = node_prev.read().unwrap();

        assert_eq!(*next, *node_prev);
    }

    fn assert_node_dependency(node: &NodeRef<VecOperation>, node_dep: &NodeRef<VecOperation>) {
        let node = node.read().unwrap();
        let next = node.dependency.as_ref().unwrap().read().unwrap();

        let node_dep = node_dep.read().unwrap();

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
        let instances = vec![Mutex::new(instance)];


        state_manager.save_instance(0, sc_address, backend, instances);
        
        state_manager
    }

    #[test]
    fn ascii_add() {
        let lhs = String::from("145").into_bytes();
        let rhs = String::from("66").into_bytes();
        let res = ascii_encoded_add(&lhs, &rhs);
        assert_eq!(res, String::from("211").into_bytes());

        let lhs = String::from("35").into_bytes();
        let rhs = String::from("-40").into_bytes();
        let res = ascii_encoded_add(&lhs, &rhs);
        assert_eq!(res, String::from("-5").into_bytes());
    }

    #[test]
    fn ascii_sub() {
        let lhs = String::from("100").into_bytes();
        let rhs = String::from("45").into_bytes();
        let res = ascii_encoded_sub(&lhs, &rhs);
        assert_eq!(res, String::from("55").into_bytes());

        let lhs = String::from("50").into_bytes();
        let rhs = String::from("100").into_bytes();
        let res = ascii_encoded_sub(&lhs, &rhs);
        assert_eq!(res, String::from("-50").into_bytes());
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
        let LastWrites {commutative, non_commutative} = schedule.get_last_writes(SC_ADDR_A, &key_bytes);
        match (commutative, non_commutative) {
            (Some(_), Some(_)) | (Some(_), None) | (None, Some(_)) => assert!(false),
            (None, None) => assert!(true),
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

        let LastWrites {commutative, non_commutative} = schedule.get_last_writes(SC_ADDR_A, &key_bytes); 
        match (commutative, non_commutative) {
            (Some(_), Some(non_comm)) | (None, Some(non_comm)) => {
                assert_eq!(*node2.read().unwrap(), *non_comm.read().unwrap());
            },
            (_, _) => assert!(false),
        };

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
        assert_eq!(deps.get(&tx1).unwrap().load(Ordering::SeqCst), 0);
        assert_eq!(deps.get(&tx2).unwrap().load(Ordering::SeqCst), 1);
        assert_eq!(deps.get(&tx3).unwrap().load(Ordering::SeqCst), 1);
        assert_eq!(deps.get(&tx4).unwrap().load(Ordering::SeqCst), 1);
        assert_eq!(deps.get(&tx5).unwrap().load(Ordering::SeqCst), 1);
        assert_eq!(deps.get(&tx6).unwrap().load(Ordering::SeqCst), 0);
        
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
        assert_eq!(node.read().unwrap().data.value, None);
    }

    // Storage | <- [Comm Read]
    // Should update the value read in the node
    #[test]
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
        assert_eq!(node.read().unwrap().data.value, Some(val));
    }

    // Storage | <- [Comm Read] <- [Comm Write]
    // Should update the value read in the node
    #[test]
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
        assert_eq!(node.read().unwrap().data.value, Some("5".as_bytes().to_vec()));
    }

    // Storage | [Non Comm Write] <- [Non Comm Read]
    #[test]
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
        assert_eq!(write_node.read().unwrap().data.value, Some(delta));

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
        assert_eq!(write_node.read().unwrap().data.value, Some(val.clone()));

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
        assert_eq!(write_node.read().unwrap().data.value, Some(delta));

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
        assert_eq!(write_node.read().unwrap().data.value, Some(delta1));

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
        assert_eq!(write_node.read().unwrap().data.value, Some(delta2));

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
        let ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), 1);

        // not added to partial_ready
        let partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
        assert!(partial_ready_q.lock().pop_front().is_none());

        // schedule head is the write node
        let sc_schedule = concurrent_schedule.schedule.schedule.get(&sc_address).unwrap();
        let head = &sc_schedule.get(&key).unwrap().head;
        assert_eq!(*head.read().unwrap().read().unwrap(), *op_node.read().unwrap());

        // schedule tail is the write node
        let tail = &sc_schedule.get(&key).unwrap().tail;
        assert_eq!(*tail.read().unwrap().read().unwrap(), *op_node.read().unwrap());

        // schedule last_non_commutative write is the write node
        let LastWrites {commutative, non_commutative } = concurrent_schedule.schedule.get_last_writes(sc_address, &key);

        match (commutative, non_commutative) {
            (None, Some(non_comm)) => {
                assert_eq!(*non_comm.read().unwrap(), *op_node.read().unwrap());
            },
            _ => assert!(false)
        }
        
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
        let ready_q = concurrent_schedule.execution_queues.ready_queue;
        assert_eq!(ready_q.lock().pop_front().unwrap(), 1);

        // tx is not in partial_ready
        let partial_ready_q = concurrent_schedule.execution_queues.partial_ready_queue;
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
                rws_uid: "A".to_owned(),
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