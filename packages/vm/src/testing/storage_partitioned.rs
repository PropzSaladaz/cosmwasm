use concurrent_map::ConcurrentMap;
use strum::Display;
use std::{fmt, sync::RwLock};
#[cfg(feature = "iterator")]
use std::collections::HashMap;
#[cfg(feature = "iterator")]
use std::ops::{Bound, RangeBounds};

use std::sync::{Arc, Mutex};

#[cfg(feature = "iterator")]
use cosmwasm_std::{Order, Record};
use dashmap::DashMap;
use num::pow::Pow;

#[cfg(feature = "iterator")]
use crate::BackendError;
use crate::{symb_exec::{ReadWrite, Commutativity}, BackendResult, GasInfo};

#[cfg(feature = "iterator")]
const GAS_COST_LAST_ITERATION: u64 = 37;

#[cfg(feature = "iterator")]
const GAS_COST_RANGE: u64 = 11;

#[cfg(feature = "iterator")]
#[derive(Default, Debug)]
struct Iter {
    data: Vec<Record>,
    position: usize,
}

// TODO - maybe implement Paolo's Idea
// - Reads do not conflict with writes
// - We then read again at the end to check if the read values weren't changed
// Use a struct like:

// struct Counter {
//     value: AtomicI32,
//     write_lock: Mutex<()>,
// }
// struct PartitionedCounter {
//     subcounters: Vec<Arc<Counter>>,
//     
// }

// And only lock when writing. 

#[derive(Debug, Display)]
pub enum ValueType {
    Partitioned {
        shifts: u8,
        partitions: Vec<Mutex<Vec<u8>>>
    },
    Single(Vec<u8>),
}

impl PartialEq for ValueType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (me, you) => me.read() == you.read()
        }
    }
}

impl ValueType {

    /// Used for testing purposes
    #[allow(dead_code)]
    fn num_partitions(&self) -> usize {
        match self {
            Self::Single(_) => 1,
            Self::Partitioned{shifts, partitions: _ } => 2u8.pow(*shifts as u32) as usize
        }
    }

    /// Works as "set all partitions". Meaning we set the item as a single value,
    /// and if the item was previously partitioned, we divide the value of the new item into the partitions
    fn set(&mut self, value: &[u8]) {
        match self {
            Self::Partitioned {
                shifts,
                partitions: _
            } =>  {
                let shifts = *shifts;
                *self = Self::Single(value.to_vec());
                self.partition(shifts);
            },
            Self::Single(vec) => {
                *vec = value.to_vec(); 
            }
        }
    }

    /// Only sets the specified partition IFF the item is partitioned.
    /// If the item is Single, then just set the Single item.
    fn set_partition(&self, value: &[u8], partition: usize) {
        match self {
            Self::Partitioned {
                shifts: _,
                partitions
            } =>  {
                let mut lock = partitions.get(partition).unwrap().lock().unwrap();
                *lock = value.to_vec();
                },
            Self::Single(_) => {
                unreachable!("Set partition should never be called on a Single item as there is not write-lock from the caller");
            }
        }
    }


    /// If is partitioned, sums all partitions.
    /// Else, returns the value directly 
    fn read(&self) -> Vec<u8> {
        match self {
            Self::Partitioned {
                shifts: _,
                partitions,
            } =>  {
                let mut total: Vec<u8> = vec![0x00; partitions.get(0).unwrap().lock().unwrap().len()];
                for part in partitions {
                    {
                        let part = part.lock().unwrap();
                        let part_val = part.as_ref();
                        total = ValueType::bitwise_add(total, part_val);
                    }
                };
                total
            },
            Self::Single(vec) => vec.clone()
        }
    }

    /// If is partitioned, read a single partition.
    /// Else, returns the value directly 
    fn read_partition(&self, partition: usize) -> Vec<u8> {
        match self {
            Self::Partitioned { shifts: _, partitions } => partitions.get(partition).unwrap().lock().unwrap().clone(),
            Self::Single(vec) => vec.clone()
        }
    }

    fn bitwise_add(lhs: Vec<u8>, rhs: &Vec<u8>) -> Vec<u8> {
        let n_bytes = lhs.len();
        let mut res: Vec<u8> = vec![0x00; n_bytes];
        let mut overflow_amount: u8 = 0;
                                                // add each byte from right to left
        for ((lhs, rhs), sum) in lhs.iter().rev().zip(
                                                    rhs.iter().rev()).zip(
                                                    res.iter_mut().rev()) {
            let mut tmp_sum: u8;
            let mut over: bool;
            let mut tmp_over: bool;

            // overflow can come either from the sum or from adding the overflow
            // after a non-overflowing sum
            //
            // lhs + rhs            lhs + rhs + overflow     
            //   1 1 <- rhs             1 1 <- lhs + rhs
            // + 1 1 <- lhs           + 0 1 <- overflow amount
            // _____                  _____
            // 1 1 0                  1 0 0
            // ^                      ^
            // |                      |
            // transport from sum     transport from overflow (after sum without overflow)

            (tmp_sum, over) = lhs.overflowing_add(*rhs);
            tmp_over = over;
            (tmp_sum, over) = tmp_sum.overflowing_add(overflow_amount);
            tmp_over = tmp_over || over;

            if tmp_over { overflow_amount = 1 }
            else        { overflow_amount = 0 }

            *sum = tmp_sum;

        };
        res
    }

    fn sum_partition(&mut self) {
        *self = Self::Single(self.read());
    }

    /// Partitions itself into ```2^n_shifts``` partitions.
    /// Partitions are always a power of 2.
    /// 
    /// Divides the initial value into the N partitions, and places the remainder
    /// in the last partition
    fn partition(&mut self, n_shifts: u8) {
        // 2 partitions             4 partitions          
        // n_shifts = 2             n_shifts = 4
        // n_shifts >> 2 = 0        n_shifts >> 2 = 1
        // mask = 0000 0001         mask = 0000 0011 
        //
        // shift bytes by 1         shift bytes by 2
        // == dividing by 2         == dividing by 4
        let mut shift_mask: u8 = 0;
        for n in 0..n_shifts {
            shift_mask += 1 << n;
        }

        // total number of partitions
        let total_part = 2usize.pow(n_shifts as u32);

        let mut partitions = vec![vec![]; total_part];

        match self {
            Self::Single(vec) => {
                // will store remainder of division
                let mut remainder: u8 = 0;

                // |-byte1--| |-byte2--
                // 0100  1101 0110 ...
                //         ^^   
                //         ||  
                // these are the bits for the next byte. 
                // Result:
                // |-byte1--| |-byte2--
                // 0001  0011 0101 ...
                //            ^^
                let mut bits_for_next_byte: u8 = 0;

                for byte in vec.iter_mut() {
                    remainder = *byte & shift_mask;

                    *byte >>= n_shifts;
                    *byte += bits_for_next_byte;

                    if n_shifts > 0 { bits_for_next_byte =  remainder << (8 - n_shifts); }
                }

                // populate all partitions with same amount
                for n in 0..(total_part-1) {
                    partitions[n] = vec.clone();
                }

                // place the excess in the last partition
                let mut remainder_vec = vec![0u8; vec.len()];
                let last = remainder_vec.len() - 1;
                remainder_vec[last] = remainder;

                partitions[total_part - 1] = ValueType::bitwise_add(vec.clone(), &remainder_vec);
            },
            _ => () 
        }

        let partitions = partitions.into_iter().map(|i| Mutex::new(i)).collect();

        *self = Self::Partitioned { shifts: n_shifts, partitions };
    }
}



// TODO - think about this:
// We use RwLock to work as a barrier for when ValueType is partitioned.
// WHenever we need to write all or read all, we lock the RwLock for write.
// Else, we lock it for read
type ConcurrentItem = Arc<RwLock<ValueType>>; 

#[derive(Default)]
pub struct MockStoragePartitioned {
    data: ConcurrentMap<Vec<u8>, ConcurrentItem>,
    #[cfg(feature = "iterator")]
    iterators: Mutex<HashMap<u32, Mutex<Iter>>>,
    n_partition_shifts: u8,
    n_partitions: u8,
}

impl MockStoragePartitioned {
    pub fn default() -> Self {
        Self::new(2)
    }

    pub fn get_item(&self, item: &[u8]) -> ConcurrentItem {
        self.data.get(item).unwrap().to_owned()
    }

    #[cfg(feature = "iterator")]
    pub fn all(&mut self, iterator_id: u32) -> BackendResult<Vec<Record>> {
        let mut out: Vec<Record> = Vec::new();
        let mut total = GasInfo::free();
        loop {
            let (result, info) = self.next(iterator_id);
            total += info;
            match result {
                Err(err) => return (Err(err), total),
                Ok(ok) => {
                    if let Some(v) = ok {
                        out.push(v);
                    } else {
                        break;
                    }
                }
            }
        }
        (Ok(out), total)
    }
}

/// Custom implementation of Storage trait, tailored to partitioned storage.
/// Only differs in gets and sets. Now we have a set/get all and a set/get partition.
pub trait PartitionedStorage: BaseStorage + cosmwasm_std::Storage + fmt::Debug {

    fn new(n_partition_shifts: u8) -> Self where Self: Sized;

    /// Reads the value of an item specified by the key.
    /// Sender address is used whenever the item is partitioned, to choose the partition we read from.
    /// Types of reads:
    ///     Commutative &  Partitioned || Commutative & !Partitioned -> lock item as read()
    ///    !Commutative &  Partitioned                               -> lock item as write()
    ///    !Commutative & !Partitioned                               -> lock item as read()
    fn get(&self, key: &[u8], sender_address: &[u8], commutative: bool, partitioned: bool) -> BackendResult<Option<Vec<u8>>>;

    /// Writes the value of an item specified by the key.
    /// Sender address is used whenever the item is partitioned, to choose the partition we read from.
    /// Types of reads:
    ///     Commutative &  Partitioned  -> lock item as read()  (we can lock to read the partitioned item, and only lock for write our partition)
    ///     Commutative & !Partitioned  -> lock item as write() (we need to lock entire item, as it is single)
    ///    !Commutative &  Partitioned  -> lock item as write() (we need to lock the entire partitioned item as we will write to all partitions)
    ///    !Commutative & !Partitioned  -> lock item as write() (we need to lock entire item, as it is single)  
    fn set(&self, key: &[u8], value: &[u8], sender_address: &[u8], commutative: bool, partitioned: bool) -> BackendResult<()>;

    /// Partition items identified by the passed keys into N partitions.
    /// N is defined as a constant.
    fn partition_items(&self, items: Vec<Vec<u8>>);

    /// Convert the specified partitioned items into single items.
    fn sum_partitioned_items(&self, items: Vec<Vec<u8>>);

}

pub trait BaseStorage {
    /// Allows iteration over a set of key/value pairs, either forwards or backwards.
    /// Returns an interator ID that is unique within the Storage instance.
    ///
    /// The bound `start` is inclusive and `end` is exclusive.
    ///
    /// If `start` is lexicographically greater than or equal to `end`, an empty range is described, mo matter of the order.
    ///
    /// This call must not change data in the storage, but creating and storing a new iterator can be a mutating operation on
    /// the Storage implementation.
    /// The implementation must ensure that iterator IDs are assigned in a deterministic manner as this is
    /// environment data that is injected into the contract.
    fn scan(
        &self,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        order: Order,
    ) -> BackendResult<u32>;

    /// Returns the next element of the iterator with the given ID.
    ///
    /// If the ID is not found, a BackendError::IteratorDoesNotExist is returned.
    ///
    /// This call must not change data in the storage, but incrementing an iterator can be a mutating operation on
    /// the Storage implementation.
    #[cfg(feature = "iterator")]
    fn next(&self, iterator_id: u32) -> BackendResult<Option<Record>>;

    /// Returns the next value of the iterator with the given ID.
    /// Since the iterator is incremented, the corresponding key will never be accessible.
    ///
    /// If the ID is not found, a BackendError::IteratorDoesNotExist is returned.
    ///
    /// The default implementation uses [`Storage::next`] and discards the key.
    /// More efficient implementations might be possible depending on the storage.
    #[cfg(feature = "iterator")]
    fn next_value(&self, iterator_id: u32) -> BackendResult<Option<Vec<u8>>> {
        let (result, gas_info) = self.next(iterator_id);
        let result = result.map(|record| record.map(|(_, v)| v));
        (result, gas_info)
    }

    /// Returns the next key of the iterator with the given ID.
    /// Since the iterator is incremented, the corresponding value will never be accessible.
    ///
    /// If the ID is not found, a BackendError::IteratorDoesNotExist is returned.
    ///
    /// The default implementation uses [`Storage::next`] and discards the value.
    /// More efficient implementations might be possible depending on the storage.
    #[cfg(feature = "iterator")]
    fn next_key(&self, iterator_id: u32) -> BackendResult<Option<Vec<u8>>> {
        let (result, gas_info) = self.next(iterator_id);
        let result = result.map(|record| record.map(|(k, _)| k));
        (result, gas_info)
    }

    /// Removes a database entry at `key`.
    ///
    /// The current interface does not allow to differentiate between a key that existed
    /// before and one that didn't exist. See https://github.com/CosmWasm/cosmwasm/issues/290
    fn remove(&self, key: &[u8]) -> BackendResult<()>;
}

impl PartitionedStorage for MockStoragePartitioned {

    fn get(&self, key: &[u8], sender_address: &[u8], commutative: bool, partitioned: bool) -> BackendResult<Option<Vec<u8>>> {
        let gas_info = GasInfo::with_externally_used(key.len() as u64);
        let item;

        // if commutative, lock RwLock for reading only as there are only 2 cases:
        // 1 - item is partitioned, we need only to read 1 partition
        //      - By locking the item as read(), we allow for other partitions to be changes while we read our own.
        // 2 - item is not partitioned, we need to read the single item
        if commutative {
            let partition = (sender_address[0] % self.n_partitions) as usize;
            item = match self.data.get(key) {
                Some(data) => Some(data.read().unwrap().read_partition(partition)),
                None => None
            };
        }
        else {
            // If read is not commutative & we need to read all partitions, we need to lock the item for write()
            // - this will disallow any threads accessing this item - only this thread accesses the partitions
            //   of this item, as we need to read all partitions with the full item locked first, and only
            //   then release the lock. Else other threads could alter some partition's value
            if partitioned {
                item = match self.data.get(key) {
                    Some(data) => Some(data.write().unwrap().read()),
                    None => None
                };
            }
            else {
                item = match self.data.get(key) {
                    Some(data) => Some(data.read().unwrap().read()),
                    None => None
                };
                
            }
        }
        (Ok(item), gas_info)
    }


    fn partition_items(&self, items: Vec<Vec<u8>>) {
        for item in items {
            let mut val = self.data.get(&item).unwrap();
            (*val).write().unwrap().partition(self.n_partition_shifts);
            self.data.insert(item, val);
        }
    }

    fn sum_partitioned_items(&self, items: Vec<Vec<u8>>) {
        for item in items {
            let mut val = self.data.get(&item).unwrap();
            (*val).write().unwrap().sum_partition();
            self.data.insert(item, val);
        }
    }

    fn set(&self, key: &[u8], value: &[u8], sender_address: &[u8], commutative: bool, partitioned: bool) -> BackendResult<()> {
        // TODO - currently we read, check if exists, if not we insert. Then we read again, modify & write
        // Needs to be more efficient!
        if !self.data.contains_key(key) {
            self.data.insert(key.to_vec(), Arc::new(RwLock::new(ValueType::Single([0u8].to_vec()))));
            if partitioned {
                self.data.get(key).unwrap().write().unwrap().partition(self.n_partition_shifts);
            }
        }

        if commutative && partitioned {
            let partition = (sender_address[0] % self.n_partitions) as usize;
            let item = self.data.get(key).unwrap();
            item.read().unwrap().set_partition(value, partition);
        }
        else {
            self.data.get(key).unwrap().write().unwrap().set(value);
        }

        let gas_info = GasInfo::with_externally_used((key.len() + value.len()) as u64);
        (Ok(()), gas_info)

    }
    
    fn new(n_partition_shifts: u8) -> Self {
        Self {
            data: ConcurrentMap::new(),
            iterators: Mutex::new(HashMap::new()),
            n_partition_shifts: n_partition_shifts,
            n_partitions: 2.pow(n_partition_shifts) as u8,
        }
    }

}

/// Implementation of cosmwasm_std::Storage is necessary as this is the storage type
/// used for smart contract's entry point calls. When parsing the RWS, we need to pass
/// a DepsMut struct, which is defined in std, thus needing an implementation of
/// cosmwasm_std::Storage. We will only use get() function from this trait.
impl cosmwasm_std::Storage for MockStoragePartitioned {
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        PartitionedStorage::get(self, key, b"", false, false).0.unwrap()
    }

    /// All code below should never be reachable
    fn range<'a>(
        &'a self,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        order: Order,
    ) -> Box<dyn Iterator<Item = Record> + 'a> {
        unreachable!()
    }

    fn set(&mut self, key: &[u8], value: &[u8]) {
        unreachable!()
    }

    fn remove(&mut self, key: &[u8]) {
        unreachable!()
    }
}

impl BaseStorage for MockStoragePartitioned {
    #[cfg(feature = "iterator")]
    fn scan(
        &self,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        order: Order,
    ) -> BackendResult<u32> {
        /* TODO */
        let gas_info = GasInfo::with_externally_used(GAS_COST_RANGE);
        let bounds = range_bounds(start, end);

        let values: Vec<Record> = match (bounds.start_bound(), bounds.end_bound()) {
            // BTreeMap.range panics if range is start > end.
            // However, this cases represent just empty range and we treat it as such.
            (Bound::Included(start), Bound::Excluded(end)) if start > end => Vec::new(),
            _ => match order {
                Order::Ascending => self.data.range(bounds).map(clone_item).collect(),
                Order::Descending => self.data.range(bounds).rev().map(clone_item).collect(),
            },
        };

        { // hold lock for self.iterators
            let mut iterators = self.iterators.lock().unwrap();
            let last_id: u32 = iterators
                .len()
                .try_into()
                .expect("Found more iterator IDs than supported");
            let new_id = last_id + 1;
            let iter = Iter {
                data: values,
                position: 0,
            };
            iterators.insert(new_id, Mutex::new(iter));
            (Ok(new_id), gas_info)
        }

    }

    #[cfg(feature = "iterator")]
    fn next(&self, iterator_id: u32) -> BackendResult<Option<Record>> {

        let iterators = self.iterators.lock().unwrap();
        let iterator = match iterators.get(&iterator_id) {
            Some(i) => i,
            None => {
                return (
                    Err(BackendError::iterator_does_not_exist(iterator_id)),
                    GasInfo::free(),
                )
            }
        };

        let mut iterator = iterator.lock().unwrap();

        let (value, gas_info): (Option<Record>, GasInfo) =
            if iterator.data.len() > iterator.position {
                let item = iterator.data[iterator.position].clone();
                (*iterator).position += 1;
                let gas_cost = (item.0.len() + item.1.len()) as u64;
                (Some(item), GasInfo::with_cost(gas_cost))
            } else {
                (None, GasInfo::with_externally_used(GAS_COST_LAST_ITERATION))
            };

        (Ok(value), gas_info)
    }

    fn remove(&self, key: &[u8]) -> BackendResult<()> {
        self.data.remove(key);
        let gas_info = GasInfo::with_externally_used(key.len() as u64);
        (Ok(()), gas_info)
    }
}

impl fmt::Debug for MockStoragePartitioned {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MockStoragePartitioned")
            .field("data", &self.data)
            .field("iterators", &self.iterators)
            .field("n_partition_shifts", &self.n_partition_shifts)
            .field("n_partitions", &self.n_partitions).finish()
    }
}

#[cfg(feature = "iterator")]
fn range_bounds(start: Option<&[u8]>, end: Option<&[u8]>) -> impl RangeBounds<Vec<u8>> {
    (
        start.map_or(Bound::Unbounded, |x| Bound::Included(x.to_vec())),
        end.map_or(Bound::Unbounded, |x| Bound::Excluded(x.to_vec())),
    )
}

#[cfg(feature = "iterator")]
/// The BTreeMap specific key-value pair reference type, as returned by BTreeMap<Vec<u8>, Vec<u8>>::range.
/// This is internal as it can change any time if the map implementation is swapped out.
type BTreeMapRecord = (Vec<u8>, ConcurrentItem);

#[cfg(feature = "iterator")]
fn clone_item(item_ref: BTreeMapRecord) -> Record {
    let (key, value) = item_ref;
    let value = value.read().unwrap();
    (key.clone(), value.read())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sum_partitions() {
        let part = ValueType::Partitioned {
            shifts: 1,
            partitions: vec![
                Mutex::new(vec![1, 255]),
                Mutex::new(vec![0, 255])
            ]
        };

        assert_eq!(part.read(), vec![2, 254]);

        let part = ValueType::Partitioned {
            shifts: 1,
            partitions: vec![
                Mutex::new(vec![0, 255, 200]),
                Mutex::new(vec![0, 0  , 100])
            ]
        };

        assert_eq!(part.read(), vec![1, 0, 44]);
    }

    #[test]
    fn partition_item() {
        let mut part = ValueType::Single(vec![255]);
        part.partition(0); // 1 partition
        assert_eq!(part.read(), vec![255]);
        assert_eq!(part.num_partitions(), 1);

        let mut part = ValueType::Single(vec![255]);
        part.partition(1); // 2 partitions
        assert_eq!(part.read(), vec![255]);
        assert_eq!(part.num_partitions(), 2);

        let mut part = ValueType::Single(vec![255]);
        part.partition(2); // 4 partitions
        assert_eq!(part.read(), vec![255]);
        assert_eq!(part.num_partitions(), 4);

        let mut part = ValueType::Single(vec![0]);
        part.partition(2); // 4 partitions
        assert_eq!(part.read(), vec![0]);
        assert_eq!(part.num_partitions(), 4);

        let mut part = ValueType::Single(vec![255]);
        part.partition(3); // 8 partitions
        assert_eq!(part.read(), vec![255]);
        assert_eq!(part.num_partitions(), 8);

        let mut part = ValueType::Single(vec![255]);
        part.partition(4); // 16 partitions
        assert_eq!(part.read(), vec![255]);
        assert_eq!(part.num_partitions(), 16);

        let mut part = ValueType::Single(vec![177, 255]);
        part.partition(1); // 2 partitions
        assert_eq!(part.read(), vec![177, 255]);
        assert_eq!(part.num_partitions(), 2);

        let mut part = ValueType::Single(vec![63, 144, 177, 255]);
        part.partition(2); // 4 partitions
        assert_eq!(part.read(), vec![63, 144, 177, 255]);
        assert_eq!(part.num_partitions(), 4);

        let mut part = ValueType::Single(vec![63, 144, 177, 255]);
        part.partition(4); // 16 partitions
        assert_eq!(part.read(), vec![63, 144, 177, 255]);
        assert_eq!(part.num_partitions(), 16);
    }

    #[test]
    fn set_value_type() {
        let mut part = ValueType::Single(vec![255]);
        part.set(&vec![123]);
        assert_eq!(part.read(), vec![123]);
        assert_eq!(part.num_partitions(), 1);

        let mut part = ValueType::Single(vec![255]);
        part.partition(1);
        part.set_partition(&vec![5], 0);
        assert_eq!(part.read_partition(0), vec![5]);
        assert_eq!(part.read_partition(1), vec![128]);
        assert_eq!(part.num_partitions(), 2);

    }

    #[test]
    fn partition_storage() {
        let storage = MockStoragePartitioned::new(2);
        
        let key = b"foo";
        let value = [1u8, 2u8, 3u8];

        storage.set(key, &value, b"", false, false).0.unwrap();

        storage.partition_items(vec![key.to_vec()]);

        let item = storage.get_item(key);

        assert_eq!(
            *item.read().unwrap(), 
            ValueType::Partitioned {
                shifts: 2,
                partitions: vec![
                    Mutex::new(vec![0, 64, 128]),
                    Mutex::new(vec![0, 64, 128]),
                    Mutex::new(vec![0, 64, 128]),
                    Mutex::new(vec![0, 64, 131]),
                ]
            }
        );

        storage.sum_partitioned_items(vec![key.to_vec()]);
        let item = storage.get_item(key);

        assert_eq!(
            *item.read().unwrap(), 
            ValueType::Single(value.to_vec())
        );
    }

    #[test]
    fn partitioned_storage_set_and_get() {
        let storage = MockStoragePartitioned::new(2);
        let key = b"foo";
        let key2 = b"foo2";
        let value = [1u8];

        // set full item
        storage.set(key, &value, b"", true, false).0.unwrap();
        storage.set(key2, &value, b"", false, true).0.unwrap();
        
        storage.partition_items(vec![key.to_vec()]);

        const VAL1: [u8; 1] = [1u8];
        const VAL2: [u8; 1] = [2u8];
        const VAL3: [u8; 1] = [3u8];
        const VAL4: [u8; 1] = [4u8];
        const SUM: [u8; 1] = [10u8];

        // set commutative & partitioned - set a different value for each partition
        storage.set(key, &VAL1, &[8u8], true, true).0.unwrap();
        storage.set(key, &VAL2, &[9u8], true, true).0.unwrap();
        storage.set(key, &VAL3, &[10u8], true, true).0.unwrap();
        storage.set(key, &VAL4, &[7u8], true, true).0.unwrap();

        // get commutative ( note that the partition flag is irrelevant here) - read value from specific partition
        let part1 = storage.get(key, &[4u8], true, true).0.unwrap().unwrap();
        let part2 = storage.get(key, &[5u8], true, false).0.unwrap().unwrap();
        let part3 = storage.get(key, &[6u8], true, true).0.unwrap().unwrap();
        let part4 = storage.get(key, &[7u8], true, false).0.unwrap().unwrap();

        assert_eq!(part1, VAL1.to_vec());
        assert_eq!(part2, VAL2.to_vec());
        assert_eq!(part3, VAL3.to_vec());
        assert_eq!(part4, VAL4.to_vec());

        // get non-commutative & partitioned - sum all sub-counters
        let full = storage.get(key, &[7u8], false, true).0.unwrap().unwrap();
        assert_eq!(full, SUM.to_vec());

        // get non-commutative & non-partitioned - read single item
        let full = storage.get(key2, &[7u8], false, false).0.unwrap().unwrap();
        assert_eq!(full, value.to_vec());

    }

    #[test]
    fn get_and_set() {
        let store = MockStoragePartitioned::default();
        assert_eq!(None, store.get(b"foo", b"", false, false).0.unwrap());
        store.set(b"foo", b"bar", b"", false, false).0.unwrap();
        assert_eq!(Some(b"bar".to_vec()), store.get(b"foo", b"", false, false).0.unwrap());
        assert_eq!(None, store.get(b"food", b"", false, false).0.unwrap());
    }

    #[test]
    fn delete() {
        let store = MockStoragePartitioned::default();
        store.set(b"foo", b"bar", b"", false, false).0.unwrap();
        store.set(b"food", b"bank", b"", false, false).0.unwrap();
        store.remove(b"foo").0.unwrap();

        assert_eq!(None, store.get(b"foo", b"", false, false).0.unwrap());
        assert_eq!(Some(b"bank".to_vec()), store.get(b"food", b"", false, false).0.unwrap());
    }

    #[test]
    #[ignore = "not_implemented_yet"]
    #[cfg(feature = "iterator")]
    fn iterator() {
        let mut store = MockStoragePartitioned::default();
        store.set(b"foo", b"bar", b"", false, false).0.expect("error setting value");

        // ensure we had previously set "foo" = "bar"
        assert_eq!(store.get(b"foo", b"", false, false).0.unwrap(), Some(b"bar".to_vec()));
        let iter_id = store.scan(None, None, Order::Ascending).0.unwrap();
        assert_eq!(store.all(iter_id).0.unwrap().len(), 1);

        // setup - add some data, and delete part of it as well
        store.set(b"ant", b"hill", b"", false, false).0.expect("error setting value");
        store.set(b"ze", b"bra", b"", false, false).0.expect("error setting value");

        // noise that should be ignored
        store.set(b"bye", b"bye", b"", false, false).0.expect("error setting value");
        store.remove(b"bye").0.expect("error removing key");

        // unbounded
        {
            let iter_id = store.scan(None, None, Order::Ascending).0.unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(
                elements,
                vec![
                    (b"ant".to_vec(), b"hill".to_vec()),
                    (b"foo".to_vec(), b"bar".to_vec()),
                    (b"ze".to_vec(), b"bra".to_vec()),
                ]
            );
        }

        // unbounded (descending)
        {
            let iter_id = store.scan(None, None, Order::Descending).0.unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(
                elements,
                vec![
                    (b"ze".to_vec(), b"bra".to_vec()),
                    (b"foo".to_vec(), b"bar".to_vec()),
                    (b"ant".to_vec(), b"hill".to_vec()),
                ]
            );
        }

        // bounded
        {
            let iter_id = store
                .scan(Some(b"f"), Some(b"n"), Order::Ascending)
                .0
                .unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(elements, vec![(b"foo".to_vec(), b"bar".to_vec())]);
        }

        // bounded (descending)
        {
            let iter_id = store
                .scan(Some(b"air"), Some(b"loop"), Order::Descending)
                .0
                .unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(
                elements,
                vec![
                    (b"foo".to_vec(), b"bar".to_vec()),
                    (b"ant".to_vec(), b"hill".to_vec()),
                ]
            );
        }

        // bounded empty [a, a)
        {
            let iter_id = store
                .scan(Some(b"foo"), Some(b"foo"), Order::Ascending)
                .0
                .unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(elements, vec![]);
        }

        // bounded empty [a, a) (descending)
        {
            let iter_id = store
                .scan(Some(b"foo"), Some(b"foo"), Order::Descending)
                .0
                .unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(elements, vec![]);
        }

        // bounded empty [a, b) with b < a
        {
            let iter_id = store
                .scan(Some(b"z"), Some(b"a"), Order::Ascending)
                .0
                .unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(elements, vec![]);
        }

        // bounded empty [a, b) with b < a (descending)
        {
            let iter_id = store
                .scan(Some(b"z"), Some(b"a"), Order::Descending)
                .0
                .unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(elements, vec![]);
        }

        // right unbounded
        {
            let iter_id = store.scan(Some(b"f"), None, Order::Ascending).0.unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(
                elements,
                vec![
                    (b"foo".to_vec(), b"bar".to_vec()),
                    (b"ze".to_vec(), b"bra".to_vec()),
                ]
            );
        }

        // right unbounded (descending)
        {
            let iter_id = store.scan(Some(b"f"), None, Order::Descending).0.unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(
                elements,
                vec![
                    (b"ze".to_vec(), b"bra".to_vec()),
                    (b"foo".to_vec(), b"bar".to_vec()),
                ]
            );
        }

        // left unbounded
        {
            let iter_id = store.scan(None, Some(b"f"), Order::Ascending).0.unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(elements, vec![(b"ant".to_vec(), b"hill".to_vec()),]);
        }

        // left unbounded (descending)
        {
            let iter_id = store.scan(None, Some(b"no"), Order::Descending).0.unwrap();
            let elements = store.all(iter_id).0.unwrap();
            assert_eq!(
                elements,
                vec![
                    (b"foo".to_vec(), b"bar".to_vec()),
                    (b"ant".to_vec(), b"hill".to_vec()),
                ]
            );
        }
    }
}