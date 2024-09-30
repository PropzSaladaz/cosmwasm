use std::rc::Rc;
use std::sync::Arc;
use cosmwasm_std::Order;
use cosmwasm_std::Record;
use lazy_static::lazy_static;
use crate::symb_exec::Commutativity;
use crate::symb_exec::ContractRWS;
use crate::BackendApi;
use crate::ConcurrentTimer;
use crate::Querier;
use crate::SCManager;
use crate::SCStorage;
use crate::{ConcurrentSchedule, GasInfo, NodeRef, ScAddr, ScheduleBuilder, TxId, VecOperation};

use crate::{symb_exec::ReadWrite, BackendResult};

use super::storage_partitioned::{BaseStorage, ConcurrentStorage};
use super::MockApi;
use super::MockQuerier;
use super::{mock_tx_operation, MockConcurrentStorage};

static DEFAULT_CONTRACT: &str = &"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

lazy_static! {
    // A static timer that tracks the total elapsed time.
    static ref TIMER: ConcurrentTimer = ConcurrentTimer::new();
}

pub fn print_storage_wrapper_times(n_threads: u16) {
    println!("STORAGE_WRAPPER ---");
    println!("timer_gets_and_sets: ~{:?} per thread", TIMER.get_value() / (n_threads as u32));
    println!("---");
}


/// Serves as a wrapper around storage, created when executing a tx
/// with some specific context, such as the RWS, the address of the sc, and so on.
/// This wrapper also stores the RWS and marks each read/write for each
/// call to keep track of the respective node in the schedule that Read/Write corresponds to.
pub struct MockStorageWrapper {
    storage: Arc<SCStorage<MockApi, MockConcurrentStorage, MockQuerier>>,
    current_storage: Option<Arc<MockConcurrentStorage>>,

    schedule: Rc<Arc<ConcurrentSchedule>>,
    tx_block_id: TxId,

    curr_sc_address: ScAddr,
    rws: Vec<ContractRWS>,
    /// used to index different SCs - indexes self.rws directly
    rws_idx: usize,
    /// used to index different Read/Write within a contract 
    /// - indexes rws inside the self.rws[rws_idx]
    rws_contract_idx: usize,
}

impl MockStorageWrapper {
    /// Used strictly for testing pruposes
    pub fn default(storage: Arc<SCStorage<MockApi, MockConcurrentStorage, MockQuerier>>) -> MockStorageWrapper {
        let mut schedule = ScheduleBuilder::new();
        // all schedules must have at least 1 operation detected by the SE
        schedule.build_from_rws(&mut vec![
            mock_tx_operation(DEFAULT_CONTRACT.to_owned(), &vec![1u8], 0, ReadWrite::write(), Commutativity::NonCommutative)
        ]);
        StorageWrapper::new(
            0, 
            storage, 
            Rc::new(Arc::new(ConcurrentSchedule::from_schedule_builder(schedule))), 
            vec![],
            "".to_owned()
        )
    }
}

impl Default for MockStorageWrapper {
    /// Used strictly fo rtesting pruposes
    fn default() -> MockStorageWrapper {
        StorageWrapper::new(
            0,  
            Arc::new(SCStorage::default()), 
            Rc::new(Arc::new(ConcurrentSchedule::new())), 
            vec![],
            "".to_owned()
        )
    }
}

/// Includes Wrapper-specific operations. Each of these functions (except get_immutable)
/// alter the current object to be updated to know which Read/Write it is currently
/// on, following the RWS sequence from the profile.
pub trait StorageWrapper: BaseStorage {
    fn new(tx_block_id: TxId, storage: Arc<SCStorage<MockApi, MockConcurrentStorage, MockQuerier>>, 
        concurrent_schedule: Rc<Arc<ConcurrentSchedule>>, rws: Vec<ContractRWS>, contract_addr: ScAddr) -> Self;

    /// Reads a key, and checks if it matches the expected operation type (read)
    /// from the RWS profile at the current position.
    /// Each read advances the current ReadWrite position in the RWS sequence
    /// Only reads a commutative read IF:
    ///  - The operation type in current position in RWS is read (as expected)
    ///  - The key being read is the same marked in the op. in current position in RWS
    fn get(&mut self, key: &[u8]) -> BackendResult<Option<Vec<u8>>>;

    /// Does not alter our current position in the RWS.
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
        self.current_storage.as_ref().unwrap().scan(start, end, order)
    }

    #[cfg(feature = "iterator")]
    fn next(&self, iterator_id: u32) -> BackendResult<Option<Record>> {
        self.current_storage.as_ref().unwrap().next(iterator_id)
    }

    fn remove(&self, key: &[u8]) -> BackendResult<()> {
        let storage = self.current_storage.as_ref().unwrap();
        BaseStorage::remove(&**storage, key)
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
    
    /// Reads an item.
    /// If the read depends on an operation from the schedule, then read from that node.
    /// Else read from storage.
    /// 
    /// When reading a value, if the current read is Commutative, then also update the value read on the node.
    /// This value will be used to compute the delta when the respective Commutative write is performed.
    fn get(&mut self, key: &[u8]) -> BackendResult<Option<Vec<u8>>> {
        #[cfg(feature = "exec_time")]
        let timer = TIMER.create_scoped_timer();

        #[cfg(feature = "debug")]
        print_with_thread_id!("Get key: {:?}", key);

        let curr_rws = if let Some(contract) = self.rws.get(self.rws_idx) {
            if let Some(rws) = contract.rws.get(self.rws_contract_idx) {
                if self.rws_contract_idx == contract.rws.len() - 1 {
                    // set next contract's rws scope
                    self.rws_idx += 1;
                    self.rws_contract_idx = 0;
                    if self.rws_idx < self.rws.len() {
                        let curr_sc_adddr = &self.rws.get(self.rws_idx).unwrap().contract_addr;
                        let storage = Arc::clone(&self.storage.get(curr_sc_adddr).unwrap().storage);
                        self.current_storage = Some(storage);
                        self.curr_sc_address = curr_sc_adddr.clone();
                    }
                }
                self.rws_contract_idx += 1;
                rws
            }
            else { unreachable!("RWS should be perfect as of now"); }
        } else { unreachable!("RWS should be perfect as of now") };


        let read_value = |operation_node: &NodeRef<VecOperation>, key: &[u8]| {
            if let Some(schedule_value) = self.schedule.get_value(
                operation_node,
                self.current_storage.as_ref().unwrap(), 
                &self.curr_sc_address, 
                key) 
            {
                let gas_info = GasInfo::with_externally_used(key.len() as u64);
                (Ok(Some(schedule_value)), gas_info)
            }
            else {
                let storage = self.current_storage.as_ref().unwrap();
                ConcurrentStorage::get(&**storage, key)
            }      
        };


        let res = match curr_rws {
            ReadWrite::Write { .. } => {
                unreachable!("Trying to read an item from storage, but the corresponding operation was a write in the predicted RWS")
            },
            ReadWrite::Read { 
                operation_node ,
                ..
            } => read_value(operation_node.as_ref().unwrap(), key)
        };

        #[cfg(feature = "exec_time")]
        TIMER.add_scoped_timer(timer);

        res
    }

    fn get_immutable(&self, key: &[u8]) -> BackendResult<Option<Vec<u8>>> {
        #[cfg(feature = "exec_time")]
        let timer = TIMER.create_scoped_timer();
        let storage = self.current_storage.as_ref().unwrap();
        let res = ConcurrentStorage::get(&**storage, key);

        #[cfg(feature = "exec_time")]
        TIMER.add_scoped_timer(timer);

        res
    }

    fn set(&mut self, key: &[u8], value: &[u8]) -> BackendResult<()> {

        #[cfg(feature = "exec_time")]
        let timer = TIMER.create_scoped_timer();

        #[cfg(feature = "debug")]
        print_with_thread_id!("Set key: {:?}", key);

        let curr_rws = if let Some(contract) = self.rws.get(self.rws_idx) {
            if let Some(rws) = contract.rws.get(self.rws_contract_idx) {
                if self.rws_contract_idx == contract.rws.len() - 1 {
                    // set next contract's rws scope
                    self.rws_idx += 1;
                    self.rws_contract_idx = 0;
                    if self.rws_idx < self.rws.len() {
                        let curr_sc_adddr = &self.rws.get(self.rws_idx).unwrap().contract_addr;
                        let storage = Arc::clone(&self.storage.get(curr_sc_adddr).unwrap().storage);
                        self.current_storage = Some(storage);
                        self.curr_sc_address = curr_sc_adddr.clone();

                    }
                }
                self.rws_contract_idx += 1;
                rws
            }
            else { unreachable!("RWS should be perfect as of now"); }
        } else { unreachable!("RWS should be perfect as of now") };

        let res = match curr_rws {
            ReadWrite::Write { 
                operation_node ,
                ..
            } => {
                self.schedule.set_value(operation_node.as_ref().unwrap(), value);
                GasInfo::with_externally_used((key.len() + value.len()) as u64)                           
            },
            ReadWrite::Read { .. } => {
                unreachable!("Trying to set an item in storage, but the corresponding operation was a read in the predicted RWS")
            },
        };

        #[cfg(feature = "exec_time")]
        TIMER.add_scoped_timer(timer);

        (Ok(()), res)
    }
    
    fn new(tx_block_id: TxId, storage: Arc<SCStorage<MockApi, MockConcurrentStorage, MockQuerier>>, concurrent_schedule: Rc<Arc<ConcurrentSchedule>>, rws: Vec<ContractRWS>, contract_addr: String) 
    -> MockStorageWrapper
    {
        // rws, as well as the storage itself can be empty in case of instantiations, where we are just spawning VMs with empty context
        let current_storage = if let Some(curr_sc) = rws.get(0) {
            Some(Arc::clone(&storage.get(&contract_addr).unwrap().storage))
        }else {
            None
        };


        Self {
            current_storage: current_storage,
            tx_block_id,
            storage,
            schedule: concurrent_schedule, 
            curr_sc_address: contract_addr,
            rws: rws,
            rws_idx: 0,
            rws_contract_idx: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{symb_exec::{Key, StorageDependency, TxRWS}, testing::mock_tx_operation, PersistentBackend, RWSContext, SEStatus, SymbolicExecutionEngine};

    use super::*;

    const SC_ADDR_A: &str = &"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    #[test]
    fn perfect_rws_get_with_no_dependencies() {
        // Tests if StorageWrapper is reading from underlying storage as there is no operation
        // it depends on

        let key = vec![1u8];
        let val = vec![13u8];
        let rws = vec![ContractRWS {
            contract_addr: SC_ADDR_A.to_string(),
            rws: vec![
                ReadWrite::Read { 
                    storage_dependency: StorageDependency::Dependent, 
                    key: Key::Bytes(key.clone()), 
                    commutativity: Commutativity::NonCommutative, 
                    operation_node: None,
            }],
        }];
        // rws of tx with idx 0
        let tx_idx = 0;

        // block with all txs
        let mut block = vec![
            RWSContext {
                rws: TxRWS {
                    storage_dependency: StorageDependency::Dependent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "A".to_owned(),
                    rws: rws,
                },
                address: SC_ADDR_A.to_owned(),
                tx_message: None,
                tx_block_id: 0
            }
        ];

        // initial storage
        let storage = Arc::new(MockConcurrentStorage::new());
        storage.set(key.as_slice(), val.as_slice()).0.unwrap();
        let sc_storage = SCStorage::new();
        let backend = PersistentBackend::<MockApi, MockConcurrentStorage, MockQuerier>::from_storage(storage);
        sc_storage.insert("".to_owned(), Arc::new(backend));

        let mut concurrent_schedule = ScheduleBuilder::new();
        concurrent_schedule.build_from_rws(&mut block);

        // We can only fetch the RWS after building the schedule, since this build alters the RWS by setting
        // the operation_node field
        let rws_tx_0 = block.get(0).unwrap().rws.rws.clone();
        
        let mut storage_wrapper = MockStorageWrapper::new(tx_idx, Arc::new(sc_storage), 
            Rc::new(Arc::new(ConcurrentSchedule::from_schedule_builder(concurrent_schedule))), rws_tx_0, "".to_owned());

        let item = storage_wrapper.get(key.as_slice());

        assert!(item.0.is_ok());
        let res = item.0.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap(), val);

        // rws_idx should advance
        assert_eq!(storage_wrapper.rws_idx, 1);
    }


    #[test]
    fn perfect_rws_get_with_dependencies() {
        // Tests if StorageWrapper is reading from the value written by the previous
        // write operation it depends on

        let key = vec![1u8];
        let val = vec![13u8];
        let val_after = vec![5u8];
        // rws of tx with idx 0
        let tx_idx_0 = 0;
        let tx_idx_1 = 1;

        // block with all txs
        let mut block = vec![
            // Tx_0 writes to the key
            RWSContext {
                rws: TxRWS {
                    storage_dependency: StorageDependency::Dependent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "A".to_owned(),
                    rws: vec![ContractRWS {
                     contract_addr: SC_ADDR_A.to_owned(),
                     rws: vec![
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Dependent, 
                            key: Key::Bytes(key.clone()), 
                            commutativity: Commutativity::NonCommutative, 
                            operation_node: None,
                        }],   
                    }] 
                },
                address: SC_ADDR_A.to_owned(),
                tx_message: None,
                tx_block_id: tx_idx_0
            },
            // Tx_1 reads from that key
            RWSContext {
                rws: TxRWS {
                    storage_dependency: StorageDependency::Dependent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "B".to_owned(),
                    rws: vec![ContractRWS {
                        contract_addr: SC_ADDR_A.to_owned(),
                        rws: vec![
                            ReadWrite::Read { 
                                storage_dependency: StorageDependency::Dependent, 
                                key: Key::Bytes(key.clone()), 
                                commutativity: Commutativity::NonCommutative, 
                                operation_node: None,
                        }],
                    }] 
                },
                address: SC_ADDR_A.to_owned(),
                tx_message: None,
                tx_block_id: tx_idx_1
            }
        ];

        // initial storage - initial value is set to 13
        let storage = Arc::new(MockConcurrentStorage::new());
        storage.set(key.as_slice(), val.as_slice()).0.unwrap();

        let sc_storage = SCStorage::new();
        let backend = PersistentBackend::<MockApi, MockConcurrentStorage, MockQuerier>::from_storage(storage);
        sc_storage.insert("".to_owned(), Arc::new(backend));
        let sc_storage = Arc::new(sc_storage);

        let mut concurrent_schedule = ScheduleBuilder::new();
        concurrent_schedule.build_from_rws(&mut block);
        let schedule_ref = Arc::new(ConcurrentSchedule::from_schedule_builder(concurrent_schedule));

        // ** simulate Tx_0 executing - WRITE ** //
        // We can only clone the RWS after building the schedule, since this build alters the RWS by setting
        // the operation_node field
        let rws_tx_0 = block.get(tx_idx_0 as usize).unwrap().rws.rws.clone();
        let mut storage_wrapper = MockStorageWrapper::new(tx_idx_0, Arc::clone(&sc_storage), 
            Rc::new(Arc::clone(&schedule_ref)), rws_tx_0, SC_ADDR_A.to_owned());
        storage_wrapper.set(key.as_slice(), val_after.as_slice()).0.unwrap();

        // rws_idx should advance
        assert_eq!(storage_wrapper.rws_idx, 1);

        // ** simulate Tx_1 executing - READ ** //
        let rws_tx_1 = block.get(tx_idx_1 as usize).unwrap().rws.rws.clone();
        let mut storage_wrapper = MockStorageWrapper::new(tx_idx_1, Arc::clone(&sc_storage), 
        Rc::new(Arc::clone(&schedule_ref)), rws_tx_1, SC_ADDR_A.to_owned());
        let item = storage_wrapper.get(key.as_slice());


        assert!(item.0.is_ok());
        let res = item.0.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap(), val_after);

        // rws_idx should advance
        assert_eq!(storage_wrapper.rws_idx, 1);
    }


    #[test]
    fn untracked_rws_get_with_no_dependencies() {
        // Tests if StorageWrapper is reading from underlying storage as this is an untracked
        // read operation that has no dependencies

        let key = vec![1u8];
        let val = vec![13u8];
        // rws of tx with idx 0
        let tx_idx = 0;

        // initial storage
        let storage = Arc::new(MockConcurrentStorage::new());
        storage.set(key.as_slice(), val.as_slice()).0.unwrap();

        let sc_storage = SCStorage::new();
        let backend = PersistentBackend::<MockApi, MockConcurrentStorage, MockQuerier>::from_storage(storage);
        sc_storage.insert("".to_owned(), Arc::new(backend));
        let sc_storage = Arc::new(sc_storage);

        let mut concurrent_schedule = ScheduleBuilder::new();
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &vec![5u8], tx_idx, ReadWrite::write(), Commutativity::NonCommutative)
        ]);

        // storagewrapper will not have any RWS sequence
        let mut storage_wrapper = MockStorageWrapper::new(tx_idx, sc_storage, 
            Rc::new(Arc::new(ConcurrentSchedule::from_schedule_builder(concurrent_schedule))), vec![], "".to_owned());

        // untracked read
        let item = storage_wrapper.get(key.as_slice());

        assert!(item.0.is_ok());
        let res = item.0.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap(), val);

        // rws_idx should not advance
        assert_eq!(storage_wrapper.rws_idx, 0);
    }


    #[test]
    fn untracked_rws_get_with_dependencies_from_same_tx() {
        // Tests if StorageWrapper is reading from previous untracked Write upon having the following sequence of
        // operations: [W] <- [R]

        let key = vec![1u8];
        let val = vec![13u8];
        let val_after = vec![5u8];
        // rws of tx with idx 0
        let tx_idx = 0;

        // initial storage
        let storage = Arc::new(MockConcurrentStorage::new());
        storage.set(key.as_slice(), val.as_slice()).0.unwrap();

        let sc_storage = SCStorage::new();
        let backend = PersistentBackend::<MockApi, MockConcurrentStorage, MockQuerier>::from_storage(storage);
        sc_storage.insert("".to_owned(), Arc::new(backend));
        let sc_storage = Arc::new(sc_storage);

        let mut concurrent_schedule = ScheduleBuilder::new();
        concurrent_schedule.build_from_rws(&mut vec![
            mock_tx_operation(SC_ADDR_A.to_owned(), &vec![5u8], tx_idx, ReadWrite::write(), Commutativity::NonCommutative)
        ]);

        // storagewrapper will not have any RWS sequence
        let mut storage_wrapper = MockStorageWrapper::new(tx_idx, sc_storage, 
            Rc::new(Arc::new(ConcurrentSchedule::from_schedule_builder(concurrent_schedule))), vec![], "".to_owned());

        // untracked write
        storage_wrapper.set(key.as_slice(), val_after.as_slice()).0.unwrap();
        // untracked read depending on previous untracked write
        let item = storage_wrapper.get(key.as_slice());

        assert!(item.0.is_ok());
        let res = item.0.unwrap();
        assert!(res.is_some());
        assert_eq!(res.unwrap(), val_after);

        // rws_idx should not advance
        assert_eq!(storage_wrapper.rws_idx, 0);
    }
}