use std::collections::HashSet;
use std::{collections::HashMap, sync::Arc};
use cosmwasm_std::Order;
use cosmwasm_std::Record;

use crate::symb_exec::Key;
use crate::symb_exec::WriteType;
use crate::GasInfo;

use crate::{symb_exec::ReadWrite, BackendResult};

use super::{BaseStorage, MockStoragePartitioned, PartitionedStorage};

/// Serves as a wrapper around storage, created when executing a tx
/// with some specific sender address.
/// When the WASM code then calls the db_write, it will use the 
/// current sender address saved in this context to choose the storage item 
/// partition to write to.
/// This wrapper also stores the RWS and marks each read/write for each
/// call to choose whether the current write/read is supposed to be
/// aimed to a single partition, or to all partitions.
#[derive(Debug)]
pub struct MockStorageWrapper {
    storage: Arc<dyn PartitionedStorage>,
    sender_address: Vec<u8>,
    rws: Vec<ReadWrite>,
    rws_idx: usize,
    partitioned_items: Arc<HashSet<Vec<u8>>>
}

impl MockStorageWrapper {
    /// Used strictly fo rtesting pruposes
    pub fn default(storage: Arc<MockStoragePartitioned>) -> MockStorageWrapper {
        Self::new(storage, String::from(""), vec![], Arc::new(HashSet::new()))
    }
}

impl Default for MockStorageWrapper {
    /// Used strictly fo rtesting pruposes
    fn default() -> MockStorageWrapper {
        Self::new(Arc::new(MockStoragePartitioned::default()), String::from(""), 
        vec![], Arc::new(HashSet::new()))
    }
}

/// Includes Wrapper-specific operations. Each of these functions (except get_immutable)
/// alter the current object to be updated to know which Read/Write it is currently
/// on, following the RWS sequence from the profile.
pub trait StorageWrapper: BaseStorage {
    // type ReturnType<'a>: 'a;

    fn new(storage: Arc<dyn PartitionedStorage>, sender_address: String, rws: Vec<ReadWrite>, partitioned_items: Arc<HashSet<Vec<u8>>>) -> Self /*Self::ReturnType<'a>*/;

    /// Reads a key, and checks if it matches the expected operation type (read)
    /// from the RWS profile at the current position.
    /// Each read advances the current ReadWrite position in the RWS sequence
    /// Only reads a commutative read IF:
    ///  - The operation type in current position in RWS is read (as expected)
    ///  - The key being read is the same marked in the op. in current position in RWS
    fn get(&mut self, key: &[u8]) -> BackendResult<Option<Vec<u8>>>;

    /// Reads from all partitions - Does not alter our current position in the RWS.
    /// used only when getting the RWS at the start of all VM execution.
    /// These reads do not use the context
    fn get_immutable(&self, key: &[u8]) -> BackendResult<Option<Vec<u8>>>;


    fn set(&mut self, key: &[u8], value: &[u8]) -> BackendResult<()>;
}

/// Storage functionality that is common both to Wrapper and to underlying partitioned storage
impl BaseStorage for MockStorageWrapper {
    fn scan(
        &self,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        order: Order,
    ) -> BackendResult<u32> {
        self.storage.scan(start, end, order)
    }

    #[cfg(feature = "iterator")]
    fn next(&self, iterator_id: u32) -> BackendResult<Option<Record>> {
        self.storage.next(iterator_id)
    }

    fn remove(&self, key: &[u8]) -> BackendResult<()> {
        BaseStorage::remove(&*self.storage, key)
    }
}

/// Redirects all operations to the self.storage.
/// Updates the rws_idx for each read/write
/// TODO - what if we have a Read non-commutative, but the current operation in RWS is a read commutative & the key matches?
///     Actual RWS: Read1(non commutative) --> Read2(commutative)
///  Predicted RWS: Read1(commutative)
/// There is a shift... Think about how to solve this. Maybe take in consideration if profile is complete or not
/// In worst case, if profile is incomplete, we treat all operations as non-commutative
impl StorageWrapper for MockStorageWrapper {

    fn get(&mut self, key: &[u8]) -> BackendResult<Option<Vec<u8>>> {

        let full_read = || {
            let commutative = false;
            let is_partitioned = self.partitioned_items.contains(key);
            PartitionedStorage::get(&*self.storage, key, &self.sender_address.as_slice(), commutative, is_partitioned)
        };

        let res = match self.rws.get(self.rws_idx) {
            Some(rws) => match rws {
                ReadWrite::Write { storage_dependency: _, key, commutativity: _ } => {
                    (Ok(Some(vec![1u8])), GasInfo::new(0, 0)) // TODO - testing only
                    // unreachable!("Trying to read an item from storage, but the corresponding operation was a write in the predicted RWS")
                },
                ReadWrite::Read { storage_dependency: _, key: key_read, commutativity } => match commutativity {
                    WriteType::Commutative => {
                        match key_read {
                            Key::Bytes(k) => {
                                if k.as_slice() == key {
                                    let commutative = true;
                                    let is_partitioned = self.partitioned_items.contains(key);
                                    PartitionedStorage::get(&*self.storage, key, &self.sender_address.as_slice(), commutative, is_partitioned)
                                }
                                else { full_read() }
                            },
                            _ => unreachable!("Key should be in bytes")
                        }
                    }
                    WriteType::NonCommutative => full_read()
                }
            },
            None => full_read()
        };
    
        self.rws_idx += 1;
        res
    }

    fn get_immutable(&self, key: &[u8]) -> BackendResult<Option<Vec<u8>>> {
        PartitionedStorage::get(&*self.storage, key, &self.sender_address.as_slice(), false, false)
    }

    fn set(&mut self, key: &[u8], value: &[u8]) -> BackendResult<()> {
        // match current Read/Write in the sequence of the RWS
        let res = match self.rws.get(self.rws_idx) {
            Some(rws) => match rws {
                ReadWrite::Write { storage_dependency: _, key: k, commutativity } => match commutativity {
                    WriteType::Commutative    => {
                        let commutative = true;
                        let is_partitioned = self.partitioned_items.contains(key);
                        PartitionedStorage::set(&*self.storage, key, value, &self.sender_address.as_slice(), commutative, is_partitioned)
                    }
                    WriteType::NonCommutative => {
                        let commutative = false;
                        let is_partitioned = self.partitioned_items.contains(key);
                        PartitionedStorage::set(&*self.storage, key, value, &self.sender_address.as_slice(), commutative, is_partitioned)
                    }
                },
                ReadWrite::Read { storage_dependency: _, key: _, commutativity: _ } => {
                    (Ok(()), GasInfo::new(0, 0)) // TODO - testing only
                    // unreachable!("Trying to set an item in storage, but the corresponding operation was a read in the predicted RWS")
                }
            },

            None => {
                let commutative: bool = false;
                let is_partitioned = self.partitioned_items.contains(key);
                PartitionedStorage::set(&*self.storage, key, value, &self.sender_address.as_slice(), commutative, is_partitioned)
            }
        };

        self.rws_idx += 1;
        res
    }
    
    fn new(storage: Arc<dyn PartitionedStorage>, sender_address: String, rws: Vec<ReadWrite>, 
        partitioned_items: Arc<HashSet<Vec<u8>>>) -> Self
        {
        Self {
            storage,
            sender_address: sender_address.into_bytes().to_vec(),
            rws: rws,
            rws_idx: 0,
            partitioned_items: partitioned_items,
        }
    }
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

#[cfg(test)]
mod tests {
    use crate::symb_exec::TransactionDependency;

    use super::*;

    #[test]
    fn get_and_set_same_sender() {
        let storage = MockStoragePartitioned::new(1);
        
        let key = b"foo";      // partitioned key
        let value = [3u8];      // initial value
        let value_2 = [12u8];   // 1st write - commutative
        let value_3 = [14u8];   // 2nd write - non commutative

        let key2 = b"foo2";    // non partitioned
        let value2 = [2u8];

        // set full item
        storage.set(key, &value, b"", false, false).0.unwrap();
        storage.set(key2, &value2, b"", false, false).0.unwrap();
        
        // only 'key' gets partitioned. 'key2' doesn't
        storage.partition_items(vec![key.to_vec()]);
        let partitioned_items = HashSet::from([(key.to_vec())]);

        // Predicted RWS by the contract
        let rws = vec![
            ReadWrite::Read  { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key.to_vec()), commutativity: WriteType::Commutative },
            ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key.to_vec()), commutativity: WriteType::Commutative },
            ReadWrite::Read  { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key.to_vec()), commutativity: WriteType::Commutative },
            ReadWrite::Read  { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key.to_vec()), commutativity: WriteType::NonCommutative },
            ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key2.to_vec()), commutativity: WriteType::NonCommutative }
        ];

        // sender's first char will get mapped to 2nd partition -> 1 % 2 = 1 (recall partitions start at index 0)
        let sender_address = std::char::from_u32(1u8 as u32).unwrap();
        let mut wrapper = MockStorageWrapper::new(
            Arc::new(storage), 
            sender_address.to_string(), 
            rws,
            Arc::new(partitioned_items)
        );

        // Real RWS during execution assuming a COMPLETE PROFILE
        // Meaning the real RWS is exactly the one predicted
        let item = wrapper.get(key).0.unwrap().unwrap();
        wrapper.set(key, value_2.as_slice()).0.unwrap();
        let item2 = wrapper.get(key).0.unwrap().unwrap();
        let item3 = wrapper.get(key).0.unwrap().unwrap();
        wrapper.set(key, value_3.as_slice()).0.unwrap();
        
        // this is an off-contract read - as it was not in the predicted RWS, it should read all counters
        let final_val = wrapper.get(key).0.unwrap().unwrap();

        // initially the value should be partitioned like: [1, 2]
        // and we are reading 2nd partition due to our sender address
        assert_eq!(item, vec![2u8]);
        // we read again 2nd partition, after writing 12u8 to 2nd partition.
        // Thus we should see value 12u8
        assert_eq!(item2, vec![12u8]);
        // we read all partitions, thus we should see the sum of [1, 12] = 13u8
        assert_eq!(item3, vec![13u8]);
        // we read all partitions after writting non-commutatively 14u8
        // Thus we should read 14u8
        assert_eq!(final_val, vec![14u8]);

    }

    #[test]
    fn get_and_set_different_senders() {
        let storage = MockStoragePartitioned::new(1);
        
        let key = b"foo";      // partitioned key
        let value = [3u8];      // initial value
        let value_2 = [12u8];   // 1st write - commutative
        let value_3 = [15u8];   // 2nd write - non commutative

        let key2 = b"foo2";    // non partitioned
        let value2 = [2u8];

        // set full item
        storage.set(key, &value, b"", false, false).0.unwrap();
        storage.set(key2, &value2, b"", false, false).0.unwrap();
        
        // only 'key' gets partitioned. 'key2' doesn't
        storage.partition_items(vec![key.to_vec()]);
        let partitioned_items = Arc::new(HashSet::from([(key.to_vec())]));
        let shared_storage: Arc<dyn PartitionedStorage> = Arc::new(storage);

        // Predicted RWS by the contract
        let rws1 = vec![
            ReadWrite::Read  { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key.to_vec()), commutativity: WriteType::Commutative },
            ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key.to_vec()), commutativity: WriteType::Commutative },
            ReadWrite::Read  { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key.to_vec()), commutativity: WriteType::Commutative },
            ReadWrite::Read  { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key.to_vec()), commutativity: WriteType::NonCommutative },
            ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key2.to_vec()), commutativity: WriteType::NonCommutative }
        ];

        // Predicted RWS by the contract
        let rws2 = vec![
            ReadWrite::Read  { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key.to_vec()), commutativity: WriteType::NonCommutative },
            ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key.to_vec()), commutativity: WriteType::NonCommutative },
            ReadWrite::Read  { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key.to_vec()), commutativity: WriteType::Commutative },
            ReadWrite::Read  { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key2.to_vec()), commutativity: WriteType::Commutative },
            ReadWrite::Write { storage_dependency: TransactionDependency::INDEPENDENT, key: Key::Bytes(key2.to_vec()), commutativity: WriteType::Commutative }
        ];

        // sender's first char will get mapped to 2nd partition -> 1 % 2 = 1 (recall partitions start at index 0)
        let sender_address1 = std::char::from_u32(1u8 as u32).unwrap();
        // sender's first char will get mapped to 1st partition -> 0 % 2 = 0 (recall partitions start at index 0)
        let sender_address2 = std::char::from_u32(0u8 as u32).unwrap();


        let mut wrapper1 = MockStorageWrapper::new(
            Arc::clone(&shared_storage), 
            sender_address1.to_string(), 
            rws1,
            Arc::clone(&partitioned_items)
        );

        let mut wrapper2 = MockStorageWrapper::new(
            Arc::clone(&shared_storage), 
            sender_address2.to_string(), 
            rws2,
            Arc::clone(&partitioned_items)
        );

        // Real RWS during execution assuming a COMPLETE PROFILE
        // Meaning the real RWS is exactly the one predicted
        let item1_1 = wrapper1.get(key).0.unwrap().unwrap();    // sender 1 - commutative
        wrapper1.set(key, value_2.as_slice()).0.unwrap();
        let item2_1 = wrapper2.get(key).0.unwrap().unwrap();    // sender 2 - non commutative
        wrapper2.set(key, value_3.as_slice()).0.unwrap();

        let item1_2 = wrapper1.get(key).0.unwrap().unwrap();    // sender 1
        let item2_2 = wrapper2.get(key).0.unwrap().unwrap();    // sender 2

        let item1_3 = wrapper1.get(key).0.unwrap().unwrap();    // sender 1
        wrapper1.set(key, value_2.as_slice()).0.unwrap();
        let item2_3 = wrapper2.get(key).0.unwrap().unwrap();    // sender 2
        wrapper2.set(key, value.as_slice()).0.unwrap();

        // this is an off-contract read - as it was not in the predicted RWS, it should read all counters
        let final_val = wrapper1.get(key).0.unwrap().unwrap();

        // initially the value should be partitioned like: [1, 2]
        // and we are reading 2nd partition due to our sender address
        assert_eq!(item1_1, vec![2u8]);
        // sender2's non commutative read will read [1, 12], summed up
        assert_eq!(item2_1, vec![13u8]);
        // we read again 2nd partition, after writing 15u8 to all
        // Thus we should see value 8u8, as 14 doesnt divides evenly for all partitiones [7u8, 8u8]
        assert_eq!(item1_2, vec![8u8]);
        // sender2 reads partition 0 - [7u8, 8u8]
        assert_eq!(item2_2, vec![7u8]);
        // sender1 reads all partitions
        assert_eq!(item1_3, vec![15u8]);
        // sender2 reads all partitions after sender has written 12u8 non commutatively
        assert_eq!(item2_3, vec![12u8]);
        // we read all partitions after writting non-commutatively 3u8 to 1st partition
        // Previous state was [6, 6], now should be [9, 6]
        assert_eq!(final_val, vec![9u8]);
    }

}