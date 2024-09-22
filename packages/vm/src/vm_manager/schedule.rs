use std::{
    fmt, i128, io::Write, sync::{Arc}
};

use dashmap::DashMap;
use parking_lot::{Mutex, Condvar, RwLock};

use crate::{symb_exec::Commutativity, testing::{ConcurrentStorage, StorageWrapper}};

#[cfg(feature = "debug_graph")]
use super::dot_schedule::{DotSchedule, NodeColor};

// size of a smart contract address
pub const ADDR_SIZE: usize = 32; 

pub type ScAddr = String;
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

    /// Waits to be notified.
    /// To be used when there is still no value set 
    pub fn wait(&self) {
        let mut started = self.lock.lock();
        while !*started {
            self.cvar.wait(&mut started);
        }
        // we won't set 'started' to false - after an operation is complete,
        // all dependent txs will read from it. There is never the need 
        // for a tx to go back to waiting state after an operation is completed
    }

    /// Notifies all waiting threads on this signal.
    /// To be used after setting the value
    pub fn notify_all(&self) {
        let mut started = self.lock.lock();
        *started = true;
        self.cvar.notify_all();
    }
}


pub trait MergeableValue: Clone + Sized + PartialEq {
    fn compute_delta(&self, old_val: &Self) -> Self;
    fn merge(&mut self, val: &Self);
}

impl MergeableValue for Vec<u8> {
    fn compute_delta(&self, other: &Self) -> Self {
        ascii_encoded_sub(self, other)
    }

    fn merge(&mut self, other: &Self) {
        *self = ascii_encoded_add(self, other);
    }
}


/// Represents an arbitrary value wrapped around a signaling
/// primitive, allowing threads to wait for the value to be set
/// if it hasnt been set yet.
/// When setting a new value, notifies all waiting threads
#[derive(Debug)]
pub struct OperationValue<V: MergeableValue> {
    pub value: Mutex<Option<V>>,
    pub condvar: Condvar,
}

impl<V: MergeableValue> PartialEq for OperationValue<V> {
    fn eq(&self, other: &Self) -> bool {
        // we need the clone, since we could be comparing the same operationValue, leading to a deadlock if we
        // try locking both at the same time (e.g. inside the == expression)
        let val_1 = self.value.lock().clone();
        let val_2 = other.value.lock().clone();
        val_1 == val_2
    }
}

impl<V: MergeableValue> OperationValue<V> {
    pub fn new() -> Self {
        OperationValue {
            value: Mutex::new(None),
            condvar: Condvar::new(),
        }
    }

    /// waits for the value to be set if it hasn't been set yet
    pub fn wait_for_value(&self) -> V {
        let mut val = self.value.lock();
        
        while val.is_none()  {
            self.condvar.wait(&mut val);
        }

        val.as_ref().unwrap().clone()
    }

    /// Used for cases when we know for sure the value has already been set
    /// Which is the case for operations within the same tx.
    pub fn get_value(&self) -> Option<V> {
        self.value.lock().clone()
    }

    /// Sets the value & notifies all waiting threads on this value.
    pub fn set_and_notify(&self, value: V) {
        let mut val = self.value.lock();
        *val = Some(value);
        self.condvar.notify_all();
    }
}



#[derive(Debug, PartialEq)]
pub struct Operation<V: MergeableValue> {
    pub operation_type: OpType,
    pub commutativity: Commutativity,
    pub tx_block_id: TxId,
    // in the future this can be made a generic parameter
    pub value: OperationValue<V>,
    // indicates if this is the first operation from a tx
    pub first_operation: bool,
}


impl<V: MergeableValue> Operation<V> {
    pub fn new(operation_type: OpType, tx_block_id: TxId, commutativity: Commutativity, first_operation: bool) -> Self {
        Self {
            operation_type,
            commutativity,
            tx_block_id,
            value: OperationValue::new(),
            first_operation
        }
    }

    pub fn set_value(&self, new_value: V) {
        self.value.set_and_notify(new_value)
    }

    pub fn wait_for_value(&self) -> V {
        self.value.wait_for_value()
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
    pub fn new_ref(operation_type: OpType, tx_block_id: TxId, commutativity: Commutativity, first_operation: bool) -> NodeRef<VecOperation> {
        Arc::new(RwLock::new(DependencyNode {
            data: Operation::new(operation_type, tx_block_id, commutativity, first_operation),
            next: None,
            prev: None,
            dependency: None,
        }))
    }
}

// Need to limit recursion. Else will result in stack overflow
impl<T: std::fmt::Debug> fmt::Debug for DependencyNode<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut debug_struct = f.debug_struct("DependencyNode");

        debug_struct.field("value", &self.data);

        if let Some(ref prev) = self.prev {
            let prev_value = &prev.read().data;
            debug_struct.field("prev", prev_value);
        } else {
            debug_struct.field("prev", &None::<i32>);
        }

        if let Some(ref next) = self.next {
            let next_value = &next.read().data;
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
                a.read().data == b.read().data
            },
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        } &&
        match (&self.prev, &other.prev) {
            (Some(a), Some(b)) => {
                a.read().data == b.read().data
            },
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        } &&
        match (&self.dependency, &other.dependency) {
            (Some(a), Some(b)) => {
                a.read().data == b.read().data
            },
            (Some(_), None) => false,
            (None, Some(_)) => false,
            (None, None) => true,
        }
    }
}

impl<T> DependencyNode<T> {
    pub fn new(value: T) -> Self {
        DependencyNode {
            data: value,
            next: None,
            prev: None,
            dependency: None,
        }
    }

    pub fn set_next(&mut self, operation_node: Option<NodeRef<T>>) {
        self.next = operation_node
    }


    pub fn set_prev(&mut self, operation_node: Option<NodeRef<T>>) {
        self.prev = operation_node
    }

    pub fn set_dependency(&mut self, operation_node: Option<NodeRef<T>>) {
        self.dependency = operation_node
    }

}

#[derive(Debug)]
pub struct LinkedList<T> {
    pub head: Arc<RwLock<NodeRef<T>>>,
    pub tail: Arc<RwLock<NodeRef<T>>>,
}

impl<T: PartialEq> PartialEq for LinkedList<T> {

    /// Runs through both linked lists & compares each item
    fn eq(&self, other: &Self) -> bool {
        return true;
        let mut head_node_self = Some(Arc::clone(&self.head.read()));
        let mut head_node_other = Some(Arc::clone(&other.head.read()));

        while head_node_self.is_some() && head_node_other.is_some() {
            let node_self = head_node_self.as_ref().unwrap().read();
            let node_other = head_node_other.as_ref().unwrap().read();         

            if node_self.data != node_other.data { println!("DATA"); return false; }
            // compare the dependency of both nodes
            if let Some(ref dependency) = node_self.dependency {
                if node_other.dependency.is_none() { println!("DEPENDENCY"); return false; }
                if node_other.dependency.as_ref().unwrap().read().data != 
                   dependency.read().data {
                    println!("DEPENDENCY");
                    return false;
                }
            }

            drop(node_self);
            drop(node_other);

            let tmp_head_self = if let Some(ref next) = head_node_self.as_ref().unwrap().read().next {
                Some(Arc::clone(&next))
            } else { None };

            let tmp_head_other = if let Some(ref next) = head_node_other.as_ref().unwrap().read().next {
                Some(Arc::clone(&next))
            } else { None };
            
            head_node_self = tmp_head_self;
            head_node_other = tmp_head_other;
        }

        if head_node_self.is_some() && head_node_other.is_none() ||
        head_node_self.is_none() && head_node_other.is_some() {
            return false;
        }

        return true;
    }
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
            let tail_lock = self.tail.read();
            let tail_item = &(*tail_lock);
            let tail_item_ref = Arc::clone(tail_item);

            let mut item_lock = item.write();
            item_lock.set_prev(Some(tail_item_ref));
        }
        

        // set tail.next = item
        {
            let mut tail_lock = self.tail.write();
            {
                let mut tail_item_lock = tail_lock.write();
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
        let mut item_right_lock = item_to_right.write();
        // fetch [L] from [R], and set [L]'s next value to [I]
        let prev_of_item_right = &item_right_lock.prev;
        match prev_of_item_right {
            Some(prev) => prev.write().set_next(Some(Arc::clone(&item_to_insert))),
            None => { // we are inserting to the left of head - need to update head
                let mut head = self.head.write();
                *head = Arc::clone(&item_to_insert);
            },
        };

        // set [I]'s prev to [L], and [I]'s next to [R]
        {
            let mut node = item_to_insert.write();
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




pub type LinkedListRef = Arc<LinkedList<VecOperation>>;
pub type SCSchedule = DashMap<Vec<u8>, LinkedListRef>;

type LastWrite = Arc<RwLock<NodeRef<VecOperation>>>;
type LastWriteMap =  DashMap<ScAddr, DashMap<Vec<u8>, LastWrite>>;


pub struct LastWrites {
    pub commutative: Option<NodeRef<VecOperation>>,
    pub non_commutative: Option<NodeRef<VecOperation>>
}

impl LastWrites {
    pub fn get_latest_write(&self) -> Option<NodeRef<VecOperation>> {
        match (&self.commutative, &self.non_commutative) {
            // If there are both a commutative & non commutative writes, pick the operation from the latest tx.
            (Some(comm), Some(non_comm)) => {
                let comm_id = comm.read().data.tx_block_id;
                let non_comm_id = non_comm.read().data.tx_block_id;

                let dependency = if comm_id > non_comm_id { Some(Arc::clone(comm)) }
                else { Some(Arc::clone(non_comm)) };

                dependency
            },
            (Some(comm), None) => Some(Arc::clone(comm)),
            (None, Some(non_comm)) => Some(Arc::clone(non_comm)),
            (None, None)    => None
        }
    }
}



#[derive(PartialEq, Debug, Copy, Clone)]
pub enum OpType {
    Read,
    Write,
}

/// Represents a schedule for some execution block:
/// SC -> key -> Linked list of operations for that item & SC
#[derive(Debug)]
pub struct Schedule {

    /// Stores a schedule, which is map of linked lists, one for each different KEY.
    /// Each linked list stores the order of operations affecting that item
    pub schedule: DashMap<ScAddr, SCSchedule>,

    /// Stores the last non-commutative write operation for each item of each SC
    /// SC -> key -> Last Write operation
    pub last_non_commutative_write: LastWriteMap,
    pub last_commutative_write: LastWriteMap
    // ^^ TODO - We should have a last_write for each tx - then when inserting a new untracked operation
    // we could directly fetch the last non-commutative write for that tx instead of running over the
    // entire list searching for it.
}

impl PartialEq for Schedule {
    fn eq(&self, other: &Self) -> bool {
        self.compare_last_comm(other) &&
        self.compare_last_non_comm(other) &&
        // self.compare_schedule(other)
        true
    }
}

impl Schedule {
    fn compare_schedule(&self, other: &Schedule) -> bool {
        if self.schedule.len() != other.schedule.len() { return false; }
        
        self.schedule.iter().all(|ref_multi| {
            let (key, set1) = ref_multi.pair();
            match other.schedule.get(key) {
                Some(set2) => {
                    set1.len() == set2.value().len() && 
                    set1.iter().all(|item| match set2.get(item.key()) {
                        // TODO - compare each node in the linked list
                        Some(linked_list) => {
                            **linked_list.value() == **item.value()
                        },
                        None => return false
                    })
                },
                None => false,
            }
        })
    }

    fn compare_last_non_comm(&self, other: &Schedule) -> bool {
        if self.last_non_commutative_write.len() != other.last_non_commutative_write.len() { return false; }
        
        self.last_non_commutative_write.iter().all(|ref_multi| {
            let (sc, set1) = ref_multi.pair();
            match other.last_non_commutative_write.get(sc) {
                Some(set2) => {
                    set1.len() == set2.len() && 
                    set1.iter().all(|item| set2.contains_key(item.key()))
                },
                None => false,
            }
        })
    }

    fn compare_last_comm(&self, other: &Schedule) -> bool {
        if self.last_commutative_write.len() != other.last_commutative_write.len() { return false; }
        
        self.last_commutative_write.iter().all(|ref_multi| {
            let (sc, set1) = ref_multi.pair();
            match other.last_commutative_write.get(sc) {
                Some(set2) => {
                    set1.len() == set2.len() && 
                    set1.iter().all(|item| set2.contains_key(item.key()))
                },
                None => false,
            }
        })
    }
}

impl Schedule {
    pub fn new() -> Self {
        Self {
            schedule: DashMap::new(),
            last_non_commutative_write: DashMap::new(),
            last_commutative_write: DashMap::new(),
        }
    }

    /// Merges 2 schedules together, assuming 'other' contains all consecutive transactions that come after 'self'.
    /// It then passes the pari of (last_write_SELF, first_operation_OTHER) to the caller as a closure, so that the caller
    /// can update any structs capturing the dependencies & update them
    pub fn merge<F>(&mut self, other: Schedule, dependent_nodes_work: &mut F)
    where 
        F: FnMut(NodeRef<VecOperation>, NodeRef<VecOperation>)
    {
        // iterate over all head operations from the 'other' schedule & set its dependencies on the 
        // last writes from the 'self' schedule
        for sc_other_entry in other.schedule.iter() {
            let sc_other = sc_other_entry.key();
            for key_other_entry in sc_other_entry.value() {
                let key_other = key_other_entry.key();
                let linked_list_other = key_other_entry.value();
                self.merge_operations(sc_other, key_other, linked_list_other, dependent_nodes_work);
            }
        }

        self.merge_last_writes(&self.last_commutative_write, other.last_commutative_write);
        self.merge_last_writes(&self.last_non_commutative_write, other.last_non_commutative_write);
    }

    /// Merges 2 LastWriteMaps, assuming the 'other' has operations that come after 'self' map, meaning when merging, 
    /// if both maps intersect on some operation, the operation in 'other' prevails over the ones in 'self', as it it
    /// the latest operation.
    fn merge_last_writes(&self, last_writes_self: &LastWriteMap, last_writes_other: LastWriteMap) {
        let addresses_other: Vec<ScAddr> = last_writes_other.iter().map(|pair| pair.key().clone()).collect();

        // Add all items from 'other' into 'self'. Overwritte if there are common items in both, since
        // 'other' comes after 'self', the last writes from it prevail
        for addr in addresses_other {
            let last_writes_other = last_writes_other.remove(&addr).unwrap().1;

            // the SC in 'other' exists in 'self' => then merge
            if let Some(mut last_writes_for_sc_self) = last_writes_self.get_mut(&addr) {
                last_writes_for_sc_self.value_mut().extend(last_writes_other);
            }
            // the SC in 'other' doesn't exist in 'self' => move from 'other' to 'self'
            else {
                last_writes_self.insert(addr, last_writes_other);
            }
        }
    }

    /// Updates the 'prev', 'next' and 'dependency' fields of both the first operation from the 'other' shedule and the
    /// last operation from the 'self' schedule for some sc_address and key
    /// 
    /// If 'self' schedule doesn't have any operations for the 'other' sc_address/key pair, just set a reference to the 'other' linked
    /// list
    fn merge_operations<F>(&self, sc_address: &ScAddr, key: &Vec<u8>, linked_list_other: &LinkedListRef, dependent_nodes_work: &mut F)
    where 
        F: FnMut(NodeRef<VecOperation>, NodeRef<VecOperation>) 
    {
        let linked_list_self = self.get_operations_linked_list(sc_address, key);
        let last_writes_self = self.get_last_writes(sc_address, key);

        let first_operation_other = Arc::clone(&linked_list_other.head.read());
        let last_operation_other = linked_list_other.tail.read();

        match linked_list_self {
            Some(linked_list_self) => {
                let last_operation_self = Arc::clone(&linked_list_self.tail.read());

                let mut node_other = first_operation_other.write();
                let mut node_self = last_operation_self.write();

                // update nodes' prev & next fields
                node_other.set_prev(Some(Arc::clone(&last_operation_self)));
                node_self.set_next(Some(Arc::clone(&first_operation_other)));

                drop(node_self);

                // update last operation from 'self' linked list
                let mut tail_self = linked_list_self.tail.write();
                *tail_self = Arc::clone(&last_operation_other);

                // update node dependency only on reads
                if node_other.data.is_read() {
                    // commutative reads can only depend on non-commutative writes
                    if node_other.data.is_commutative() && last_writes_self.non_commutative.is_some() {
                        let last_non_comm_write_self = last_writes_self.non_commutative.unwrap();
                        node_other.dependency = Some(last_non_comm_write_self);
                        drop(node_other); // drop lock before sending node to closure
                        dependent_nodes_work(last_operation_self, first_operation_other);
                    }
                    // non commutative reads may depend on either commutative or non commutative writes
                    else if !node_other.data.is_commutative() {
                        if let Some(last_write) = last_writes_self.get_latest_write() {
                            node_other.dependency = Some(last_write);
                            drop(node_other); // drop lock before sending node to closure
                            dependent_nodes_work(last_operation_self, first_operation_other);
                        }
                    }
                }
            },
            // there was no last operation on that sc, on that key, thus we need to initialize it
            // just create a reference to the 'other' linked list
            None => {
                self.schedule
                    .entry(sc_address.clone()).or_insert(DashMap::new())
                    .entry(key.clone()).or_insert(Arc::clone(linked_list_other));
            },
        }
    }

    /// Sets the entries of the schedule & last_write (there will be 1 last_write for each key in a SC)
    /// for the chosen SC address
    pub fn create_if_not_exists(&mut self, sc_address: &ScAddr) {
        if !self.schedule.contains_key(sc_address) {
            self.schedule.insert(sc_address.clone(), DashMap::new());
        }
        if !self.last_non_commutative_write.contains_key(sc_address) {
            self.last_non_commutative_write.insert(sc_address.clone(), DashMap::new());
        }
    }

    pub fn get_operations_linked_list(&self, sc_address: &ScAddr, key: &Vec<u8>) -> Option<LinkedListRef> {
        self.schedule.get(sc_address)
            .and_then(|sc| sc.get(key)
            .and_then(|key| Some(Arc::clone(&key.value()))))
    }

    /// Return at most 2 writes - One Commutative and one Non COmmutative that represent the latest writes of each type
    /// for some SC and some key.
    /// 
    /// Depending on the Read operation comming after each of those writes, we may want to mark a dependency either on
    /// the Commutative or the Non Commutative write.
    /// 
    /// If the Read is Comm -> Mark dependency on the latest Non Commutative write
    /// If the read is Non COmmutative -> Mark dependency on the latest of both (can be wither Comm or NonCOmm write)
    pub fn get_last_writes(&self, sc_address: &ScAddr, key: &Vec<u8>) -> LastWrites {
        let non_commutative = match self.last_non_commutative_write.get(sc_address) {
            Some(non_comm_writes) => match non_comm_writes.get(key) {
                Some(last_write) => Some(Arc::clone(&last_write.read())),
                None => None,
            },
            None => None,
        };

        let commutative = match self.last_commutative_write.get(sc_address) {
            Some(comm_writes) => match comm_writes.get(key) {
                Some(last_write) => Some(Arc::clone(&last_write.read())),
                None => None,
            },
            None => None,
        };

        LastWrites { commutative, non_commutative }
    }

    /// Appends a new operation to the end of the list of the specified KEY in the specified SC.
    /// If the operation is write - updates last_write
    pub fn append(&mut self, sc_address: &ScAddr, key: &Vec<u8>, operation_node: NodeRef<VecOperation>, op_type: OpType, commutativity: Commutativity) {
        let sc_schedule = self.schedule.get(sc_address).unwrap();
        
        // append node ref to linked list
        match sc_schedule.get(key) {
            Some(list) => list.append(Arc::clone(&operation_node)),
            None => {
                let new_linked_list = Arc::new(LinkedList::new(Arc::clone(&operation_node)));
                sc_schedule.insert(key.clone(), new_linked_list);
            },
        };
        self.update_last_write(sc_address, key, operation_node, op_type, commutativity);
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
    /// 
    /// Although both op_type and commutativity are already captured in operation_node, we pass it as args to avoid locking the RwLock
    pub fn update_last_write(&self, sc_address: &ScAddr, key: &Vec<u8>, operation_node: NodeRef<VecOperation>, op_type: OpType, commutativity: Commutativity) {

        // Aux function -> update a last write map (either the commutative or non commutative write map) with the new last write operation
        // clone the node with an Arc
        let set_write_if_not_exists = |last_write_tracker: &LastWriteMap, operation_node| {
            if !last_write_tracker.contains_key(sc_address) {
                last_write_tracker.insert(sc_address.clone(), DashMap::new());
            }
            let sc_last_write = last_write_tracker.get(sc_address).unwrap();
            let operation = sc_last_write.get(key); 
            match operation  {
                Some(last_write) => {
                    let mut last_write = last_write.write();
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
                if commutativity == Commutativity::Commutative {
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
    pub fn insert_untracked_operation(&self, sc_address: &ScAddr, key: &Vec<u8>, tx_id: TxId, operation_node: NodeRef<VecOperation>, op_type: OpType, commutativity: Commutativity) {
        let schedule = self.schedule.entry(sc_address.clone()).or_insert(DashMap::new());
        let linked_list = schedule.get(key) ;

        // if there is a linked-list (if there is any, then it must have at least 1 element by default)
        if let Some(linked_list) = linked_list {
            // TODO - Optimization!! We should store the last_non_commutative_write per each tx number
            // and we would only need to check if that last wrtie exists - then mark dependency on it. Else, 
            // read from storage
            // TODO - Optimization - We should also have the last operation node from each tx for each SC - avoid searching all operations within a SC
            // (can be benefitial for long chains - lots of operations for a single key)
            let mut prev_node: Option<NodeRef<VecOperation>> = None;
            let mut node_ref = Arc::clone(&linked_list.tail.read());
            let mut tmp_node;
            let mut highest_non_commutative_write: Option<NodeRef<VecOperation>> = None; 

            loop {
                {
                    let node = node_ref.read();
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
                    operation_node.write().set_dependency(Some(write));
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
            self.update_last_write(sc_address, &key, operation_node, op_type, commutativity);
        }

    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use parking_lot::RwLock;
    use serial_test::serial;

    use crate::{symb_exec::Commutativity, vm_manager::schedule::{ascii_encoded_add, ascii_encoded_sub, DependencyNode, LinkedList, OpType, Operation}, LastWrites, Schedule};

    use super::{NodeRef, ScAddr, VecOperation};

    const CONTRACT: &[u8] = include_bytes!("../../custom_contracts/empty-contract/target/wasm32-unknown-unknown/release/contract.wasm");
    const SC_ADDR_A: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";


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
    #[serial]
    fn linked_list_append() {
        let operation: Operation<Vec<u8>> = Operation::new(OpType::Read, 1, Commutativity::NonCommutative, true);
        let node = Arc::new(RwLock::new(DependencyNode::new(operation)));
        let linked_list = LinkedList::new(Arc::clone(&node));

        assert_eq!(*linked_list.head.read().read(), *node.read());
        assert_eq!(*linked_list.tail.read().read(), *node.read());

        let operation2 = Operation::new(OpType::Write, 2, Commutativity::NonCommutative, true);
        let node2 = Arc::new(RwLock::new(DependencyNode::new(operation2)));
        linked_list.append(Arc::clone(&node2));

        assert_eq!(*linked_list.head.read().read(), *node.read());
        assert_eq!(*linked_list.tail.read().read(), *node2.read());

        assert_node_next(&node, &node2);
        assert_node_prev(&node2, &node);
    }

    #[test]
    #[serial]
    fn linked_list_insert() {
        // setup linked list with 2 elements
        let operation = Operation::new(OpType::Read, 1, Commutativity::NonCommutative, true);
        let node = Arc::new(RwLock::new(DependencyNode::new(operation)));
        let linked_list = LinkedList::new(Arc::clone(&node));

        let operation2 = Operation::new(OpType::Write, 2, Commutativity::NonCommutative, true);
        let node2 = Arc::new(RwLock::new(DependencyNode::new(operation2)));
        linked_list.append(Arc::clone(&node2));

        // create new operation
        let operation3 = Operation::new(OpType::Write, 3, Commutativity::NonCommutative, true);
        let node3 = Arc::new(RwLock::new(DependencyNode::new(operation3)));

        linked_list.insert_to_left_of(Arc::clone(&node3), Arc::clone(&node));

        assert_eq!(*linked_list.head.read().read(), *node3.read());
        assert_eq!(*linked_list.tail.read().read(), *node2.read());

        assert_node_next(&node3, &node);
        assert_node_next(&node, &node2);

        assert_node_prev(&node, &node3);
        assert_node_prev(&node2, &node);

        // create new operation
        let operation4 = Operation::new(OpType::Write, 4, Commutativity::NonCommutative, true);
        let node4 = Arc::new(RwLock::new(DependencyNode::new(operation4)));

        linked_list.insert_to_left_of(Arc::clone(&node4), Arc::clone(&node2));

        assert_eq!(*linked_list.head.read().read(), *node3.read());
        assert_eq!(*linked_list.tail.read().read(), *node2.read());

        assert_node_next(&node3, &node);
        assert_node_next(&node, &node4);
        assert_node_next(&node4, &node2);

        assert_node_prev(&node, &node3);
        assert_node_prev(&node4, &node);
        assert_node_prev(&node2, &node4);
    }

    #[test]
    #[serial]
    fn schedule_append() {
        let mut schedule = Schedule::new();
        let key_bytes = vec![1u8];

        schedule.create_if_not_exists(&SC_ADDR_A.to_owned());

        // create a read
        let operation = Operation::new(OpType::Read, 1, Commutativity::NonCommutative, true);
        let node = Arc::new(RwLock::new(DependencyNode::new(operation)));

        schedule.append(&SC_ADDR_A.to_owned(), &key_bytes, Arc::clone(&node), OpType::Read, Commutativity::NonCommutative);

        // 1 contract
        assert_eq!(schedule.schedule.len(), 1);
        {                                                                       // because of this mutable borrow :(
            // 1 key
            let created_contract_schedule = schedule.schedule.get(&SC_ADDR_A.to_owned()).unwrap();
            assert_eq!(created_contract_schedule.len(), 1);
        }

        // since we added a read, last_write should return None
        let LastWrites {commutative, non_commutative} = schedule.get_last_writes(&SC_ADDR_A.to_owned(), &key_bytes);
        match (commutative, non_commutative) {
            (Some(_), Some(_)) | (Some(_), None) | (None, Some(_)) => assert!(false),
            (None, None) => assert!(true),
        }

        // create a write
        let operation2 = Operation::new(OpType::Write, 2, Commutativity::NonCommutative, true);
        let node2 = Arc::new(RwLock::new(DependencyNode::new(operation2)));

        schedule.append(&SC_ADDR_A.to_owned(), &key_bytes, Arc::clone(&node2), OpType::Write, Commutativity::NonCommutative);

        // 1 sc
        assert_eq!(schedule.schedule.len(), 1);
        // 1 key
        let created_contract_schedule = schedule.schedule.get(&SC_ADDR_A.to_owned()).unwrap();
        assert_eq!(created_contract_schedule.len(), 1);

        let LastWrites {commutative, non_commutative} = schedule.get_last_writes(&SC_ADDR_A.to_owned(), &key_bytes); 
        match (commutative, non_commutative) {
            (Some(_), Some(non_comm)) | (None, Some(non_comm)) => {
                assert_eq!(*node2.read(), *non_comm.read());
            },
            (_, _) => assert!(false),
        };

        // run over linked list
        let linked_list = created_contract_schedule.get(&key_bytes).unwrap();
        let node_head = Arc::clone(&*linked_list.head.read());
        assert_eq!(*node_head.read(), *node.read());
        assert_eq!(*node_head.read().next.as_ref().unwrap().read(), *node2.read());
    }
}