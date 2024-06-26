use std::{collections::{HashMap, HashSet, VecDeque}, fmt, sync::{Arc, Mutex, RwLock}};

use dashmap::DashMap;

use crate::symb_exec::{Key, ReadWrite};

use super::vm_manager::RWSContext;

// RwLock is needed since we may need to change the next field at runtime
type NodeRef<T> = Arc<RwLock<DependencyNode<T>>>;

/// Represents a node in the LinkedList
struct DependencyNode<T> {
    value: T,
    next: Option<NodeRef<T>>,
    prev: Option<NodeRef<T>>,
    dependency: Option<NodeRef<T>>
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
struct LinkedList<T> {
    head: Arc<RwLock<NodeRef<T>>>,
    tail: Arc<RwLock<NodeRef<T>>>,
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

#[derive(PartialEq, Debug)]
enum OpType {
    Read,
    Write,
}


#[derive(PartialEq, Debug)]
struct Operation {
    operation_type: OpType,
    tx_block_id: TxId,
}

impl Operation {
    fn new(operation_type: OpType, tx_block_id: TxId) -> Self {
        Self {
            operation_type,
            tx_block_id
        }
    }
}


type LinkedListRef = Arc<LinkedList<Operation>>;
type SCSchedule = DashMap<Vec<u8>, LinkedListRef>;

type LastWrite = Arc<RwLock<NodeRef<Operation>>>;

/// Represents a schedule for some execution block:
/// SC -> key -> Linked list of operations for that item & SC
#[derive(Debug)]
struct Schedule {
    schedule: DashMap<String, SCSchedule>,
    /// Stores the last write operation for each item of each SC
    /// SC -> key -> Last Write operation
    last_write: DashMap<String, DashMap<Vec<u8>, LastWrite>>
}

impl Schedule {
    fn new() -> Self {
        Self {
            schedule: DashMap::new(),
            last_write: DashMap::new(),
        }
    }
}

impl Schedule {
    fn create_if_not_exists(&mut self, sc_address: String) {
        self.schedule.entry(sc_address.clone()).or_insert(DashMap::new());
        self.last_write.entry(sc_address).or_insert(DashMap::new());
    }

    fn find_last_write(&self, sc_address: &String, key: &Vec<u8>) -> Option<NodeRef<Operation>> {
        match self.last_write.get(sc_address).unwrap().get(key) {
            Some(last_write) => Some(Arc::clone(&last_write.read().unwrap())),
            None => None,
        }
    }

    fn append(&mut self, sc_address: &String, key: &Vec<u8>, operation_node: NodeRef<Operation>, op_type: OpType) {
        let sc_schedule = self.schedule.get(sc_address).unwrap();
        
        // append node ref to linked list
        match sc_schedule.get(key) {
            Some(list) => list.append(Arc::clone(&operation_node)),
            None => {
                let new_linked_list = Arc::new(LinkedList::new(Arc::clone(&operation_node)));
                sc_schedule.insert(key.clone(), new_linked_list);
            },
        };

        // Update last write
        match op_type {
            OpType::Read => (),
            OpType::Write => {
                let sc_last_write = self.last_write.get(sc_address).unwrap();
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
}

type TxId = u16;

#[derive(Debug)]
pub struct ConcurrentSchedule {
    pub deps: DashMap<TxId, u16>,

    /// stores the txs that depend on some tx
    /// Tx -> Set of txs depending on it
    pub dependent_txs: DashMap<TxId, HashSet<TxId>>,
    /// stores the txs that have their 1st operation depending on it
    /// Tx -> Set of txs which their 1st operation depends on this tx
    pub partial_ready_tx: DashMap<TxId, HashSet<TxId>>,

    // msg idx in the sequence of messages in current block
    pub ready_queue: Mutex<VecDeque<TxId>>,
    pub partial_ready_queue: Mutex<VecDeque<TxId>>,

    /// mapping of SC_address -> key -> linked list of operations
    pub schedule: Schedule,
}


impl ConcurrentSchedule {
    fn new() -> Self {
        ConcurrentSchedule {
            deps: DashMap::new(),
            ready_queue: Mutex::new(VecDeque::new()),
            partial_ready_queue: Mutex::new(VecDeque::new()),
            schedule: Schedule::new(),
            dependent_txs: DashMap::new(),
            partial_ready_tx: DashMap::new(),
        }
    }

    /// Builds an execution schedule from a sequence of RWS's per messages.
    /// This RWS will first be sorted to have all RWSs that do not depend on storage and are complete to come first,
    /// and only after comes all the RWSs that are either incomplete, or depend on storage.
    /// 
    /// Then run over each RWS & insert it in the schedule marking the dependencies between operations & transactions
    fn build_from_rws(&mut self, block: &Vec<RWSContext>) {
        for tx in block {

            let mut first_operation = true;
            let tx_id = tx.tx_block_id;
            let contract = &tx.address;

            for operation in &tx.rws.rws {
                match operation {
                    ReadWrite::Read { 
                        storage_dependency: _, 
                        key, 
                        commutativity: _ 
                    } => {
                        let key_bytes = match key {
                            Key::Bytes(bytes) => bytes,
                            _ => unreachable!("Key should be bytes at this stage"),
                        };

                        self.update_schedule_on_read_operation(first_operation, tx_id, contract, key_bytes);
                    }
                    ReadWrite::Write { 
                        storage_dependency: _, 
                        key, 
                        commutativity: _ 
                    } => {
                        let key_bytes = match key {
                            Key::Bytes(bytes) => bytes,
                            _ => unreachable!("Key should be bytes at this stage"),
                        };

                        self.update_schedule_on_write_operation(first_operation, tx_id, contract, key_bytes)
                    }
                };

                if first_operation {
                    first_operation = false;
                }
            }

            if self.deps.get(&tx_id).is_none() { // no dependencies
                self.ready_queue.lock().unwrap().push_back(tx_id);

                // Remove it from partial_ready
                let mut idx = 0;
                let mut queue = self.partial_ready_queue.lock().unwrap();
                for item in queue.iter() {
                    if *item == tx_id { break; }
                    idx += 1;
                }
                queue.remove(idx);
            }
        }
    }

    fn update_schedule_on_read_operation(&mut self, first_operation: bool, tx_id: TxId, contract: &String, key_bytes: &Vec<u8>) {
        // create a new operation node
        let operation = Operation::new(OpType::Read, tx_id);
        let mut op_node = DependencyNode::new(operation);

        // create empty schedule for this SC
        self.schedule.create_if_not_exists(contract.clone());

        // Find last write operation
        match self.schedule.find_last_write(&contract, &key_bytes) {
            Some(write) => {
                // set new operation's dependency on previous write
                op_node.dependency = Some(Arc::clone(&write));

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
                    let mut tx_dependencies = self.deps.entry(tx_id).or_insert(0);
                    *tx_dependencies += 1;

                }  // Else, if last write was done by our tx, just append it to schedule

            },
            // No previous write
            None => {
                if first_operation {
                    self.partial_ready_queue.lock().unwrap().push_back(tx_id);
                }
            }
        };

        let concurrent_op_node = Arc::new(RwLock::new(op_node));
        self.schedule.append(contract, key_bytes, concurrent_op_node, OpType::Read);

    }

    fn update_schedule_on_write_operation(&mut self, first_operation: bool, tx_id: TxId, contract: &String, key_bytes: &Vec<u8>) {
        // create a new operation node
        let operation = Operation::new(OpType::Write, tx_id);
        let mut op_node = DependencyNode::new(operation);

        // create empty schedule for this SC
        self.schedule.create_if_not_exists(contract.clone());
        // append to schedule
        let concurrent_op_node = Arc::new(RwLock::new(op_node));
        self.schedule.append(contract, key_bytes, concurrent_op_node, OpType::Write);
        if first_operation {
            self.partial_ready_queue.lock().unwrap().push_back(tx_id);
        }
    }
}


#[cfg(test)]
mod tests {
    use std::sync::{Arc, RwLock};

    use crate::{
        symb_exec::{Commutativity, Key, ReadWrite, StorageDependency, TxRWS}, 
        vm_manager::vm_manager::{InstantiatedEntryPoint, RWSContext, VMMessage}, 
        ConcurrentBackend, ConcurrentSchedule, SEStatus
    };

    use super::{DependencyNode, LinkedList, NodeRef, OpType, Operation, Schedule};

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

    #[test]
    fn linked_list_append() {
        let operation = Operation::new(OpType::Read, 1);
        let node = Arc::new(RwLock::new(DependencyNode::new(operation)));
        let linked_list = LinkedList::new(Arc::clone(&node));

        assert_eq!(*linked_list.head.read().unwrap().read().unwrap(), *node.read().unwrap());
        assert_eq!(*linked_list.tail.read().unwrap().read().unwrap(), *node.read().unwrap());

        let operation2 = Operation::new(OpType::Write, 2);
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
        let operation = Operation::new(OpType::Read, 1);
        let node = Arc::new(RwLock::new(DependencyNode::new(operation)));
        let linked_list = LinkedList::new(Arc::clone(&node));

        let operation2 = Operation::new(OpType::Write, 2);
        let node2 = Arc::new(RwLock::new(DependencyNode::new(operation2)));
        linked_list.append(Arc::clone(&node2));

        // create new operation
        let operation3 = Operation::new(OpType::Write, 3);
        let node3 = Arc::new(RwLock::new(DependencyNode::new(operation3)));

        linked_list.insert_to_left_of(Arc::clone(&node3), Arc::clone(&node));

        assert_eq!(*linked_list.head.read().unwrap().read().unwrap(), *node3.read().unwrap());
        assert_eq!(*linked_list.tail.read().unwrap().read().unwrap(), *node2.read().unwrap());

        assert_node_next(&node3, &node);
        assert_node_next(&node, &node2);

        assert_node_prev(&node, &node3);
        assert_node_prev(&node2, &node);

        // create new operation
        let operation4 = Operation::new(OpType::Write, 4);
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
        let contract_addr = String::from("a");
        let key_bytes = vec![1u8];

        schedule.create_if_not_exists(contract_addr.clone());

        // create a read
        let operation = Operation::new(OpType::Read, 1);
        let node = Arc::new(RwLock::new(DependencyNode::new(operation)));

        schedule.append(&contract_addr, &key_bytes, Arc::clone(&node), OpType::Read);

        // 1 contract
        assert_eq!(schedule.schedule.len(), 1);
        {                                                                       // because of this mutable borrow :(
            // 1 key
            let created_contract_schedule = schedule.schedule.get(&contract_addr).unwrap();
            assert_eq!(created_contract_schedule.len(), 1);
        }

        // since we added a read, last_write should return None
        match schedule.find_last_write(&contract_addr, &key_bytes) {
            Some(_) => assert!(false),
            None => assert!(true),
        }

        // create a write
        let operation2 = Operation::new(OpType::Write, 2);
        let node2 = Arc::new(RwLock::new(DependencyNode::new(operation2)));

        schedule.append(&contract_addr, &key_bytes, Arc::clone(&node2), OpType::Write);

        // 1 sc
        assert_eq!(schedule.schedule.len(), 1);
        // 1 key
        let created_contract_schedule = schedule.schedule.get(&contract_addr).unwrap();
        assert_eq!(created_contract_schedule.len(), 1);

        if let Some(node) = schedule.find_last_write(&contract_addr, &key_bytes) {
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
        concurrent_schedule.build_from_rws(&vec![
            RWSContext {
                address: String::from("a"),
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: "a".to_owned(),
                    message: br#"{
                        "AddOne": {}
                    }"#.to_vec(),
                    code_id: 0,
                    sender_address: String::from("a"),
                },),
                tx_block_id: 1,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws: vec![
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(vec![1u8]), 
                            commutativity: Commutativity::Commutative
                        }
                    ]
                }
            }
        ]);

        let deps = concurrent_schedule.deps;
        // tx_block_id should have 0 dependencies
        assert!(deps.get(&1).is_none());
        
        // pop only available tx - tx with id 1
        let ready_q = concurrent_schedule.ready_queue;
        assert_eq!(ready_q.lock().unwrap().pop_front().unwrap(), 1);

        let partial_ready_q = concurrent_schedule.partial_ready_queue;
        let mut locked_partial = partial_ready_q.lock().unwrap();
        assert!(locked_partial.pop_front().is_none())

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
        concurrent_schedule.build_from_rws(&vec![

            // Tx1: R(A), W(A), W(B), R(C), W(C)
            RWSContext {
                address: String::from("a"),
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: "a".to_owned(),
                    message: br#""#.to_vec(),
                    code_id: 0,
                    sender_address: String::from("a"),
                },),
                tx_block_id: tx1,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_a.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_a.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_b.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_c.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_c.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                    ]
                }
            },

            // Tx2: R(D), W(A), R(B), W(B)
            RWSContext {
                address: String::from("a"),
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: "a".to_owned(),
                    message: br#""#.to_vec(),
                    code_id: 0,
                    sender_address: String::from("a"),
                },),
                tx_block_id: tx2,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_d.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_a.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_b.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_b.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                    ]
                }
            },

            // Tx3: R(A), W(A)
            RWSContext {
                address: String::from("a"),
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: "a".to_owned(),
                    message: br#""#.to_vec(),
                    code_id: 0,
                    sender_address: String::from("a"),
                },),
                tx_block_id: tx3,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_a.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_a.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                    ]
                }
            },

            // Tx4: R(C), W(C)
            RWSContext {
                address: String::from("a"),
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: "a".to_owned(),
                    message: br#""#.to_vec(),
                    code_id: 0,
                    sender_address: String::from("a"),
                },),
                tx_block_id: tx4,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_c.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_c.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                    ]
                }
            },

            // Tx5: R(B), W(B)
            RWSContext {
                address: String::from("a"),
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: "a".to_owned(),
                    message: br#""#.to_vec(),
                    code_id: 0,
                    sender_address: String::from("a"),
                },),
                tx_block_id: tx5,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_b.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_b.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                    ]
                }
            },

            // Tx6: R(D), W(D)
            RWSContext {
                address: String::from("a"),
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: "a".to_owned(),
                    message: br#""#.to_vec(),
                    code_id: 0,
                    sender_address: String::from("a"),
                },),
                tx_block_id: tx6,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_d.clone()), 
                            commutativity: Commutativity::NonCommutative
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key_d.clone()), 
                            commutativity: Commutativity::NonCommutative
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
        assert!(deps.get(&tx1).is_none());
        assert_eq!(*deps.get(&tx2).unwrap(), 1);
        assert_eq!(*deps.get(&tx3).unwrap(), 1);
        assert_eq!(*deps.get(&tx4).unwrap(), 1);
        assert_eq!(*deps.get(&tx5).unwrap(), 1);
        assert!(deps.get(&tx6).is_none());
        
        // READY: { Tx1, Tx6 }
        let ready_q = concurrent_schedule.ready_queue;
        assert_eq!(ready_q.lock().unwrap().pop_front().unwrap(), tx1);
        assert_eq!(ready_q.lock().unwrap().pop_front().unwrap(), tx6);

        // PARTIAL_READY: { Tx2 }
        let partial_ready_q = concurrent_schedule.partial_ready_queue;
        let mut locked_partial = partial_ready_q.lock().unwrap();
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

}
