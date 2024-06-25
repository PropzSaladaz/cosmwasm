use std::{collections::{HashMap, HashSet, VecDeque}, sync::{Arc, Mutex, RwLock}};

use dashmap::DashMap;

use crate::symb_exec::{Key, ReadWrite};

use super::vm_manager::RWSContext;

// RwLock is needed since we may need to change the next field at runtime
type NodeRef<T> = Arc<RwLock<Node<T>>>;

/// Represents a node in the LinkedList
#[derive(Debug)]
struct Node<T> {
    value: T,
    next: Option<NodeRef<T>>,
    prev: Option<NodeRef<T>>,
}

impl<T> Node<T> {
    fn new(value: T) -> Self {
        Node {
            value: value,
            next: None,
            prev: None,
        }
    }

    fn set_next(&mut self, operation_node: Option<NodeRef<T>>) {
        self.next = operation_node
    }


    fn set_prev(&mut self, operation_node: Option<NodeRef<T>>) {
        self.prev = operation_node
    }

}

struct LinkedList<T> {
    head: Arc<RwLock<NodeRef<T>>>,
    tail: Arc<RwLock<NodeRef<T>>>,
}

impl<T> LinkedList<T> {
    fn new(item: NodeRef<T>) -> Self {
        let item = Arc::new(RwLock::new(Arc::clone(&item)));
        LinkedList {
            head: Arc::clone(&item),
            tail: Arc::clone(&item),
        }
    }

    fn append(&self, item: NodeRef<T>) {
        // set prev item
        let tail_ref = Arc::clone(&self.tail.read().unwrap());
        item.write().unwrap().set_prev(Some(tail_ref));
        // set next item
        let mut tail = self.tail.write().unwrap();
        tail.write().unwrap().set_next(Some(Arc::clone(&item)));
        // set new tail
        *tail = Arc::clone(&item);
    }

    /// Given 2 nodes: [I] and [R]
    /// This method inserts [I] to the left of [R] in the linked list:
    /// 
    /// BEFORE
    /// [L]->[R]
    /// 
    /// AFTER
    /// [L]->[I]->[R]
    fn insert_to_left_of(&self, item_to_insert: NodeRef<T>, item_to_right: NodeRef<T>) {
        // fetch [L] from [R], and set [L]'s next value to [I]
        let prev_of_item_right = &item_to_right.read().unwrap().prev;
        match prev_of_item_right {
            Some(prev) => prev.write().unwrap().set_next(Some(Arc::clone(&item_to_insert))),
            None => (),
        };

        // set [I]'s prev to [L], and [I]'s next to [R]
        let mut node = item_to_insert.write().unwrap();
        node.set_prev(match prev_of_item_right {
            Some(prev) => Some(Arc::clone(prev)),
            None => None,
        });
        node.set_next(Some(Arc::clone(&item_to_right)));

        // set [R]'s prev to [I]
        item_to_right.write().unwrap().set_prev(Some(Arc::clone(&item_to_right)));
    }
}

enum OpType {
    Read,
    Write,
}



struct Operation {
    operation_type: OpType,
    tx_block_id: u16,
    
}

type LinkedListRef = Arc<LinkedList<Operation>>;
type SCSchedule = DashMap<Vec<u8>, LinkedListRef>;

type OperationRef = Arc<RwLock<Operation>>;
type LastWrite = Arc<RwLock<OperationRef>>;

/// Represents a schedule for some execution block:
/// SC -> key -> Linked list of operations for that item & SC
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

    fn find_last_write(&self, sc_address: &String, key: &Vec<u8>) -> Option<OperationRef> {
        match self.last_write.get(sc_address).unwrap().get(key) {
            Some(last_write) => Some(Arc::clone(&last_write.read().unwrap())),
            None => None,
        }
    }
}

type TxId = u16;

pub struct ConcurrentSchedule {
    pub deps: DashMap<u8, u16>,

    /// stores the txs that depend on some tx
    /// Tx -> Set of txs depending on it
    dependent_txs: DashMap<TxId, HashSet<TxId>>,

    // msg idx in the sequence of messages in current block
    pub ready: Mutex<VecDeque<TxId>>,
    pub partial_ready: Mutex<VecDeque<TxId>>,

    /// mapping of SC_address -> key -> linked list of operations
    pub schedule: Schedule,
}


impl ConcurrentSchedule {
    fn new() -> Self {
        ConcurrentSchedule {
            deps: DashMap::new(),
            ready: Mutex::new(VecDeque::new()),
            partial_ready: Mutex::new(VecDeque::new()),
            schedule: Schedule::new(),
            dependent_txs: DashMap::new(),
        }
    }

    /// Builds an execution schedule from a sequence of RWS's per messages.
    /// This RWS will first be sorted to have all RWSs that do not depend on storage and are complete to come first,
    /// and only after comes all the RWSs that are either incomplete, or depend on storage.
    /// 
    /// Then run over each RWS & insert it in the schedule marking the dependencies between operations & transactions
    fn build_from_rws(&mut self, block: &Vec<RWSContext>, partitioned_items: HashMap<String, HashSet<Vec<u8>>>) {
        for tx in block {
            let contract = &tx.address;
            for operation in &tx.rws.rws {
                match operation {
                    ReadWrite::Read { 
                        storage_dependency, 
                        key, 
                        commutativity 
                    } => {
                        // create empty schedule for this SC
                        self.schedule.create_if_not_exists(contract.clone());

                        let key_bytes = match key {
                            Key::Bytes(bytes) => bytes,
                            _ => unreachable!("Key should be bytes at this stage"),
                        };

                        let lastWrite = self.schedule.find_last_write(&contract, &key_bytes);
                        match lastWrite {
                            Some(write) => (),
                                // if ()
                            // No previous write
                            None => {

                            }
                        }

                    },
                    ReadWrite::Write { 
                        storage_dependency, 
                        key, 
                        commutativity 
                    } => {

                    }
                }
            }
        }
    }
}