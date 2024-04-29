use std::collections::BTreeMap;
#[cfg(feature = "iterator")]
use std::collections::HashMap;
use std::ops::Deref;
#[cfg(feature = "iterator")]
use std::ops::{Bound, RangeBounds};

use std::sync::{Arc, Mutex};

#[cfg(feature = "iterator")]
use cosmwasm_std::{Order, Record};

#[cfg(feature = "iterator")]
use crate::BackendError;
use crate::{BackendResult, GasInfo, Storage};

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

#[derive(Debug, Eq, PartialEq)]
enum ValueType {
    Partitioned(Vec<Vec<u8>>),
    Single(Vec<u8>),
}

impl ValueType {

    /// Reads the Vec<u8> independently of which variant it is.
    /// If is partitioned, sums all partitions.
    /// Else, returns the value directly 
    fn read(&self) -> Vec<u8> {
        match self {
            Self::Partitioned(partitions) =>  {
                let mut total: Vec<u8> = vec![0x00; partitions.get(0).unwrap().len()];
                for part in partitions {
                    total = ValueType::bitwise_add(total, part);
                };
                total
            },
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

                for n in 0..(total_part-1) {
                    partitions[n] = vec.clone();
                }

                let mut remainder_vec = vec![0u8; vec.len()];
                let last = remainder_vec.len() - 1;
                remainder_vec[last] = remainder;

                partitions[total_part - 1] = ValueType::bitwise_add(vec.clone(), &remainder_vec);
            },
            _ => () 
        }

        *self = Self::Partitioned(partitions);
    }
}

// TODO - think about this:
// Wouldn't it be better to use mutrex for partitioned items (since we know they are mostly writes
// but use ReadWriteLocks for single items as we know they may have sus«bstancial reads?)
type ConcurrentItem = Arc<Mutex<ValueType>>; 

#[derive(Default, Debug)]
pub struct MockStoragePartitioned {
    data: BTreeMap<Vec<u8>, ConcurrentItem>,
    #[cfg(feature = "iterator")]
    iterators: HashMap<u32, Iter>,
}

impl MockStoragePartitioned {
    pub fn new() -> Self {
        MockStoragePartitioned::default()
    }

    fn get_item(&self, item: &[u8]) -> ConcurrentItem {
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


/// Implementation of cosmwasm_std::Storage is necessary as this is the storage type
/// used for smart contract's entry point calls. When parsing the RWS, we need to pass
/// a DepsMut struct, which is defined in std, thus needing an implementation of
/// cosmwasm_std::Storage
impl cosmwasm_std::Storage for MockStoragePartitioned {
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        Storage::get(self, key).0.unwrap()
    }

    fn range<'a>(
        &'a self,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        order: Order,
    ) -> Box<dyn Iterator<Item = Record> + 'a> {
        todo!()
    }

    fn set(&mut self, key: &[u8], value: &[u8]) {
        Storage::set(self, key, value).0.unwrap()
    }

    fn remove(&mut self, key: &[u8]) {
        Storage::remove(self, key).0.unwrap()
    }
}

impl Storage for MockStoragePartitioned {
    fn get(&self, key: &[u8]) -> BackendResult<Option<Vec<u8>>> {
        
        let gas_info = GasInfo::with_externally_used(key.len() as u64);

        let item = match self.data.get(key) {
            Some(data) => Some(data.lock().unwrap().read()),
            None => None
        };

        // TODO
        println!("Got item: {:?}    from: {:?}", item.clone(), String::from_utf8(key.to_owned()));
        
        (Ok(item), gas_info)
    }


    fn partition_items(&mut self, items: Vec<Vec<u8>>) {
        const N_PARTITION_SHIFTS: u8 = 2; // 4 partitions 
        for item in items {
            self.data.entry(item).and_modify(|item| 
                (*item).lock().unwrap().partition(N_PARTITION_SHIFTS));
        }
    }

    fn sum_partitioned_items(&mut self, items: Vec<Vec<u8>>) {
        for item in items {
            self.data.entry(item).and_modify(|item| 
                (*item).lock().unwrap().sum_partition());
        }
    }
    

    
    #[cfg(feature = "iterator")]
    fn scan(
        &mut self,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        order: Order,
    ) -> BackendResult<u32> {
        /* 
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

        let last_id: u32 = self
            .iterators
            .len()
            .try_into()
            .expect("Found more iterator IDs than supported");
        let new_id = last_id + 1;
        let iter = Iter {
            data: values,
            position: 0,
        };
        self.iterators.insert(new_id, iter);

        (Ok(new_id), gas_info)*/
        (Ok(1), GasInfo::with_externally_used(GAS_COST_RANGE))
    }

    #[cfg(feature = "iterator")]
    fn next(&mut self, iterator_id: u32) -> BackendResult<Option<Record>> {
        let iterator = match self.iterators.get_mut(&iterator_id) {
            Some(i) => i,
            None => {
                return (
                    Err(BackendError::iterator_does_not_exist(iterator_id)),
                    GasInfo::free(),
                )
            }
        };

        let (value, gas_info): (Option<Record>, GasInfo) =
            if iterator.data.len() > iterator.position {
                let item = iterator.data[iterator.position].clone();
                iterator.position += 1;
                let gas_cost = (item.0.len() + item.1.len()) as u64;
                (Some(item), GasInfo::with_cost(gas_cost))
            } else {
                (None, GasInfo::with_externally_used(GAS_COST_LAST_ITERATION))
            };

        (Ok(value), gas_info)
    }

    fn set(&mut self, key: &[u8], value: &[u8]) -> BackendResult<()> {
        
        println!("Inserted item: {:?}     at: {:?}", value, String::from_utf8(key.to_owned()));

        self.data.insert(key.to_vec(), Arc::new(Mutex::new(ValueType::Single(value.to_vec()))));
        let gas_info = GasInfo::with_externally_used((key.len() + value.len()) as u64);
        (Ok(()), gas_info)
    }

    fn remove(&mut self, key: &[u8]) -> BackendResult<()> {
        self.data.remove(key);
        let gas_info = GasInfo::with_externally_used(key.len() as u64);
        (Ok(()), gas_info)
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
type BTreeMapRecordRef<'a> = (&'a Vec<u8>, &'a Vec<u8>);

#[cfg(feature = "iterator")]
fn clone_item(item_ref: BTreeMapRecordRef) -> Record {
    let (key, value) = item_ref;
    (key.clone(), value.clone())
}

#[cfg(test)]
mod tests {
    use serde_json::Value;

    use super::*;

    #[test]
    fn sum_partitions() {
        let part = ValueType::Partitioned(vec![
            vec![1, 255],
            vec![0, 255]
        ]);

        assert_eq!(part.read(), vec![2, 254]);

        let part = ValueType::Partitioned(vec![
            vec![0, 255, 200],
            vec![0, 0  , 100]
        ]);

        assert_eq!(part.read(), vec![1, 0, 44]);
    }

    #[test]
    fn partition_item() {
        let mut part = ValueType::Single(vec![255]);
        part.partition(0); // 1 partition
        assert_eq!(part.read(), vec![255]);

        let mut part = ValueType::Single(vec![255]);
        part.partition(1); // 2 partitions
        assert_eq!(part.read(), vec![255]);

        let mut part = ValueType::Single(vec![255]);
        part.partition(2); // 4 partitions

        let mut part = ValueType::Single(vec![255]);
        part.partition(3); // 8 partitions
        assert_eq!(part.read(), vec![255]);

        let mut part = ValueType::Single(vec![255]);
        part.partition(4); // 8 partitions
        assert_eq!(part.read(), vec![255]);

        let mut part = ValueType::Single(vec![177, 255]);
        part.partition(1); // 2 partitions
        assert_eq!(part.read(), vec![177, 255]);

        let mut part = ValueType::Single(vec![63, 144, 177, 255]);
        part.partition(2); // 4 partitions
        assert_eq!(part.read(), vec![63, 144, 177, 255]);

        let mut part = ValueType::Single(vec![63, 144, 177, 255]);
        part.partition(4); // 4 partitions
        assert_eq!(part.read(), vec![63, 144, 177, 255]);
    }

    #[test]
    fn partition_storage() {
        let mut storage = MockStoragePartitioned::new();
        
        let key = b"foo";
        let value = [1u8, 2u8, 3u8];

        storage.set(key, &value).0.unwrap();

        storage.partition_items(vec![key.to_vec()]);

        let item = storage.get_item(key);

        assert_eq!(
            *item.lock().unwrap(), 
            ValueType::Partitioned(vec![
                vec![0, 64, 128],
                vec![0, 64, 128],
                vec![0, 64, 128],
                vec![0, 64, 131],
            ])
        );

        storage.sum_partitioned_items(vec![key.to_vec()]);
        let item = storage.get_item(key);

        assert_eq!(
            *item.lock().unwrap(), 
            ValueType::Single(value.to_vec())
        );
    }

    #[test]
    fn get_and_set() {
        let mut store = MockStoragePartitioned::new();
        assert_eq!(None, store.get(b"foo").0.unwrap());
        store.set(b"foo", b"bar").0.unwrap();
        assert_eq!(Some(b"bar".to_vec()), store.get(b"foo").0.unwrap());
        assert_eq!(None, store.get(b"food").0.unwrap());
    }

    #[test]
    fn delete() {
        let mut store = MockStoragePartitioned::new();
        store.set(b"foo", b"bar").0.unwrap();
        store.set(b"food", b"bank").0.unwrap();
        store.remove(b"foo").0.unwrap();

        assert_eq!(None, store.get(b"foo").0.unwrap());
        assert_eq!(Some(b"bank".to_vec()), store.get(b"food").0.unwrap());
    }

    #[test]
    #[ignore = "not_implemented_yet"]
    #[cfg(feature = "iterator")]
    fn iterator() {
        let mut store = MockStoragePartitioned::new();
        store.set(b"foo", b"bar").0.expect("error setting value");

        // ensure we had previously set "foo" = "bar"
        assert_eq!(store.get(b"foo").0.unwrap(), Some(b"bar".to_vec()));
        let iter_id = store.scan(None, None, Order::Ascending).0.unwrap();
        assert_eq!(store.all(iter_id).0.unwrap().len(), 1);

        // setup - add some data, and delete part of it as well
        store.set(b"ant", b"hill").0.expect("error setting value");
        store.set(b"ze", b"bra").0.expect("error setting value");

        // noise that should be ignored
        store.set(b"bye", b"bye").0.expect("error setting value");
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
