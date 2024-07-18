use crossbeam_skiplist::SkipMap;
use std::{fmt};
#[cfg(feature = "iterator")]
use std::collections::HashMap;
#[cfg(feature = "iterator")]
use std::ops::{Bound, RangeBounds};

use parking_lot::Mutex;

#[cfg(feature = "iterator")]
use cosmwasm_std::{Order, Record};

#[cfg(feature = "iterator")]
use crate::BackendError;
use crate::{ BackendResult, GasInfo};

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

#[derive(Default)]
pub struct MockConcurrentStorage {
    data: SkipMap<Vec<u8>, Vec<u8>>,
    #[cfg(feature = "iterator")]
    iterators: Mutex<HashMap<u32, Mutex<Iter>>>,
}

impl MockConcurrentStorage {
    pub fn default() -> Self {
        Self::new()
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
/// cosmwasm_std::Storage. We will only use get() function from this trait.
impl cosmwasm_std::Storage for MockConcurrentStorage {
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        if let Some(val) = self.data.get(key) {
            Some(val.value().clone())
        }
        else {
            None
        }
    }

    /// All code below should never be reached
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

/// Represents a concurrent Storage that is to be used within a StorageWrapper
/// This trait differs from StorageWrapper since here get/set do not mutate any other fields beside the storage
/// The get/set of the StorageWrapper will mutate the current idx in the RWS
pub trait ConcurrentStorage: BaseStorage + fmt::Debug + cosmwasm_std::Storage {
    /// Creates an empty storage
    fn new() -> Self where Self: Sized;
    /// 'Non mutable' get, used to get the respective item from storage
    fn get(&self, key: &[u8]) -> BackendResult<Option<Vec<u8>>>;
    /// 'Non mutable' set, used to set an item in storage.
    /// Multiple sets may be called concurrently - solved using locking
    fn set(&self, key: &[u8], value: &[u8]) -> BackendResult<()>;

}

impl ConcurrentStorage for MockConcurrentStorage {
    fn new() -> Self where Self: Sized {
        MockConcurrentStorage {
            data: SkipMap::new(),
            iterators: Mutex::new(HashMap::new()),
        }
    }

    fn get(&self, key: &[u8]) -> BackendResult<Option<Vec<u8>>> {
        let gas_info = GasInfo::with_externally_used(key.len() as u64);
        if let Some(val) = self.data.get(key) {
            (Ok(Some(val.value().clone())), gas_info)
        }
        else {
            (Ok(None), gas_info)
        }
        
    }

    fn set(&self, key: &[u8], value: &[u8]) -> BackendResult<()> {
        self.data.insert(key.to_vec(), value.to_vec());
        let gas_info = GasInfo::with_externally_used((key.len() + value.len()) as u64);
        (Ok(()), gas_info)
    }
}

/// Represents base fuctionality for both Storage and StorageWrapper - both will have this functionality in common
/// Neither get() or set() methods are here since they differ in terms of mutability between Storage and StorageWrapper
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

impl<T: BaseStorage> BaseStorage for &T {

    fn scan(
        &self,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        order: Order,
    ) -> BackendResult<u32> {
        (**self).scan(start, end, order)
    }

    #[cfg(feature = "iterator")]
    fn next(&self, iterator_id: u32) -> BackendResult<Option<Record>> {
        (**self).next(iterator_id)
    }

    fn remove(&self, key: &[u8]) -> BackendResult<()> {
        (**self).remove(key)
    }
}

impl BaseStorage for MockConcurrentStorage {

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
            let mut iterators = self.iterators.lock();
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

        let iterators = self.iterators.lock();
        let iterator = match iterators.get(&iterator_id) {
            Some(i) => i,
            None => {
                return (
                    Err(BackendError::iterator_does_not_exist(iterator_id)),
                    GasInfo::free(),
                )
            }
        };

        let mut iterator = iterator.lock();

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

impl fmt::Debug for MockConcurrentStorage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MockConcurrentStorage")
            .field("data", &self.data)
            .field("iterators", &self.iterators)
            .finish()
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
type BTreeMapRecord<'a> = crossbeam_skiplist::map::Entry<'a, Vec<u8>, Vec<u8>>;

#[cfg(feature = "iterator")]
fn clone_item(item_ref: BTreeMapRecord) -> Record {
    (item_ref.key().clone(), item_ref.value().to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_and_set() {
        let store = MockConcurrentStorage::default();
        assert_eq!(None, store.get(b"foo").0.unwrap());
        store.set(b"foo", b"bar").0.unwrap();
        assert_eq!(Some(b"bar".to_vec()), store.get(b"foo").0.unwrap());
        assert_eq!(None, store.get(b"food").0.unwrap());
    }

    #[test]
    fn delete() {
        let store = MockConcurrentStorage::default();
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
        let mut store = MockConcurrentStorage::default();
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