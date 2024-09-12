use std::{collections::{BTreeMap, HashMap, VecDeque}, sync::{mpsc::{self, Receiver, Sender}, Arc, Barrier}, thread, time::{Duration, Instant}};

use parking_lot::Mutex;

use crate::{print_with_thread_id, vm_manager::serial_schedule::ScheduleBuilder, TxId};

use super::{concurrent_schedule, ConcurrentSchedule, RWSContext, Schedule};

struct ThreadData {
    pub barrier: Barrier,
    pub data: Mutex<Option<ScheduleData>>,
}

impl ThreadData {
    fn new() -> Self {
        ThreadData {
            barrier: Barrier::new(2),
            data: Mutex::new(Some(ScheduleData::new())),
        }
    }
}

/// Structure to be sent via channel communication between threads
/// during schedule build
struct ScheduleData {
    schedule: Option<ScheduleBuilder>,
    txs: Option<Vec<RWSContext>>,
}

impl ScheduleData {
    fn new() -> Self {
        ScheduleData {
            schedule: None,
            txs: None,
        }
    }
}

pub struct ParallelScheduleBuilder {
}

impl ParallelScheduleBuilder {
    /// Builds an execution schedule from a sequence of RWS's per messages.
    /// Run over each RWS & insert it in the schedule marking the dependencies between operations & transactions.
    /// 
    /// The schedule is built via multithreading, using a binary-merging approach where each thread
    /// is given a subset of the txs & builds a partial schedule for it, & then some threads do the merging
    /// also in parallel, going up the binary tree. Thread 0 then receives the final merged schedule
    pub fn build_from_rws(block: &mut Vec<RWSContext>, n_threads: u16) -> ConcurrentSchedule {
        let mut total_txs = block.len() as u16;

        // avoid thread creation for 0 txs or 1 thread (notice the 'total_txs==1' condition since we
        // would drop the number of threads to 1 if total_txs is 1)
        if total_txs == 0 || n_threads == 1 || total_txs == 1 {
            let mut concurrent_schedule = ConcurrentSchedule::new();
            concurrent_schedule.build_from_rws(block);
            return concurrent_schedule;
        }

        // do not launch more threads than tx in the block
        let n_threads = if total_txs < n_threads { total_txs } 
        else { n_threads };

        let binary_tree_levels = (n_threads as f64).log2().ceil() as u16;
        let min_txs_per_thread = total_txs / n_threads;

        // Used to keep track of which other threads some thread needs to wait for & merge before sending its result
        let mut ordered_senders_for_thread_id = HashMap::with_capacity(n_threads as usize);

        let mut thread_states = Vec::with_capacity(n_threads as usize);
        
        // create channels & set senders for each thread
        for i in 0..n_threads {
            ordered_senders_for_thread_id.insert(i, VecDeque::new());
            // set current thread as a sender for the respective thread to which i needs to send to
            // thread 0 cannot set itself as sender to any other thread, since it will only merge results from other threads
            // thus the match for Some
            if let Some(send_to_id) = ParallelScheduleBuilder::get_send_to_thread_id(i, binary_tree_levels) {
                let senders_for_thread = ordered_senders_for_thread_id.get_mut(&send_to_id).unwrap();
                senders_for_thread.push_back(i);
            }
            thread_states.push(ThreadData::new());
        }

        let shared_states = Arc::new(thread_states);
        
        let mut handles = vec![];
        // create the threads & move the channel send/recv endpoints accordingly
        for i in 0..n_threads {

            // compute remaining txs by remaining threads
            let txs_for_current_thread = if total_txs % (n_threads - i) != 0 { min_txs_per_thread + 1 }
            else { min_txs_per_thread };
            total_txs -= txs_for_current_thread;

            // extract txs from the block for current thread
            let tx_subset: Vec<RWSContext> = block.drain(0..(txs_for_current_thread as usize)).collect();
            // let subset_ids: Vec<TxId> = tx_subset.clone().into_iter().map(|rws| rws.tx_block_id).collect();
            // print_with_thread_id!("Txs for this thread: {:?}", subset_ids);
            let ordered_senders = ordered_senders_for_thread_id.remove(&i).unwrap();

            let shared_states = Arc::clone(&shared_states);

            handles.push(thread::spawn(move || {
                ParallelScheduleBuilder::thread_work(i, shared_states, tx_subset, ordered_senders);
            }));
        }

        shared_states[0].barrier.wait(); // wait for thread 0 to finish

        for handle in handles {
            handle.join().unwrap();
        }
        
        let data = shared_states[0].data.lock().take().unwrap();
        let concurrent_schedule = ConcurrentSchedule::from_schedule_builder(data.schedule.unwrap(), n_threads);

        *block = data.txs.unwrap();
        concurrent_schedule
    }


    /// Given the current thread and the total binary tree levels, returns the
    /// leaf node id to which the current thread should send its result to
    fn get_send_to_thread_id(current_thread: u16, binary_tree_levels: u16) -> Option<u16> {

        for n in 0..binary_tree_levels {
            let k = 2u16.pow(n as u32);
            if (current_thread / k) % 2 != 0 {
                return Some(current_thread - k);
            }
        }
        None
    }

    /// Waits for all partial_schedules for this thread, & only after sends its data via the passed channel.
    /// Keeps a local cache since it may receive schedules out of order.
    /// Merging must always be done lower thread ids first
    fn thread_work(thread_id: u16, shared_states: Arc<Vec<ThreadData>>,mut tx_subset: Vec<RWSContext>, mut ordered_senders: VecDeque<u16>) {

        // #[cfg(feature = "exec_time")]
        // let schedule_build_timer = Instant::now();
        
        // let mut partial_schedule = ConcurrentSchedule::new();
        let mut partial_schedule = ScheduleBuilder::new();
        partial_schedule.build_from_rws(&mut tx_subset);

        // #[cfg(feature = "exec_time")]
        // println!("Thread {:?} - Schedule build time: {:?}", thread_id, schedule_build_timer.elapsed());

        // #[cfg(feature = "exec_time")]
        // let mut schedule_merge_time = Duration::ZERO;
        // #[cfg(feature = "exec_time")]
        // let mut total_merges = 0;



        // while there is some thread we need to wait the partial_schedule from
        while let Some(wait_for) = ordered_senders.pop_front() {

            shared_states[wait_for as usize].barrier.wait();

            // println!("Thread {:?} merging data from {:?}", thread_id, data.thread_id);

            // #[cfg(feature = "exec_time")]
            // let schedule_merge_timer = Instant::now();
            let data = shared_states[wait_for as usize].data.lock().take().unwrap();
            partial_schedule.merge(data.schedule.unwrap());
            tx_subset.extend(data.txs.unwrap());

            // #[cfg(feature = "exec_time")]
            // ParallelScheduleBuilder::add_elapsed_time_and_increase_merge_counter(
                // &mut total_merges, &mut schedule_merge_time, &schedule_merge_timer);

        }

        let final_data = ScheduleData {
            schedule: Some(partial_schedule),
            txs: Some(tx_subset),
        };

        let mut lock = shared_states[thread_id as usize].data.lock();
        *lock = Some(final_data);
        drop(lock);

        shared_states[thread_id as usize].barrier.wait();

    }

    #[cfg(feature = "exec_time")]
    fn add_elapsed_time_and_increase_merge_counter(merge_counter: &mut u16, schedule_merge_time: &mut Duration, schedule_merge_timer: &Instant) {
        *merge_counter += 1;
        *schedule_merge_time += schedule_merge_timer.elapsed();
    }
}


#[cfg(test)]
mod tests {
    use crate::{symb_exec::{Commutativity, Key, StorageDependency, TxRWS}, testing::mock_tx_operation, ConcurrentSchedule, InstantiatedEntryPoint, OpType, RWSContext, ReadWrite, SEStatus, ScAddr, VMMessage};

    use super::ParallelScheduleBuilder;

    const SC_ADDR_A: ScAddr = *b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    const KEY_A: [u8; 1] = [1u8];
    const KEY_B: [u8; 1] = [2u8];
    const KEY_C: [u8; 1] = [3u8];
    const KEY_D: [u8; 1] = [4u8];

    const TX_1: usize = 0;
    const TX_2: usize = 1;
    const TX_3: usize = 2;
    const TX_4: usize = 3;
    const TX_5: usize = 4;
    const TX_6: usize = 5;

    fn mock_block() -> Vec<RWSContext> {




        vec![
            // TX_1: R(A), W(A), W(B), R(C), W(C)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: TX_1,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "A".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_A.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_A.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_B.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_C.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_C.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },

            // TX_2: R(D), W(A), R(B), W(B)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: TX_2,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "B".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_D.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_A.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_B.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_B.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },

            // TX_3: R(A), W(A)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: TX_3,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "C".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_A.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_A.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },

            // TX_4: R(C), W(C)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: TX_4,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "D".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_C.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_C.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },

            // TX_5: R(B), W(B)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: TX_5,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "E".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_B.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_B.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },

            // TX_6: R(D), W(D)
            RWSContext {
                address: SC_ADDR_A,
                tx_message: Some(VMMessage::Invocation {
                    entry_point: InstantiatedEntryPoint::Execute,
                    contract_address: SC_ADDR_A,
                    message: br#""#.to_vec(),
                    code_id: 0,
                },),
                tx_block_id: TX_6,
                rws: TxRWS {
                    storage_dependency: StorageDependency::Independent,
                    profile_status: SEStatus::Complete,
                    rws_uid: "F".to_owned(),
                    rws: vec![
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_D.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(KEY_D.to_vec()), 
                            commutativity: Commutativity::NonCommutative,
                            operation_node: None,
                        },
                    ]
                }
            },
        ]
    }

    #[test]
    fn one_thread_one_tx() {
        let tx = mock_tx_operation(SC_ADDR_A, &KEY_A.to_vec(), TX_1, ReadWrite::write(), Commutativity::NonCommutative);
        let mut block = vec![tx];
        let mut block_2 = block.clone();

        let parallel_schedule = ParallelScheduleBuilder::build_from_rws(&mut block, 1);

        let mut sequential_schedule = ConcurrentSchedule::new();
        sequential_schedule.build_from_rws(&mut block_2);

        assert_eq!(parallel_schedule, sequential_schedule);
    }

    #[test]
    fn parallel_2_threads() {
        let parallel_schedule = ParallelScheduleBuilder::build_from_rws(&mut mock_block(), 2);

        let mut sequential_schedule = ConcurrentSchedule::new();
        sequential_schedule.build_from_rws(&mut mock_block());

        assert_eq!(parallel_schedule, sequential_schedule);
    }

    #[test]
    fn parallel_4_threads() {
        let parallel_schedule = ParallelScheduleBuilder::build_from_rws(&mut mock_block(), 4);

        let mut sequential_schedule = ConcurrentSchedule::new();
        sequential_schedule.build_from_rws(&mut mock_block());

        assert_eq!(parallel_schedule, sequential_schedule);
    }

    #[test]
    fn parallel_8_threads() {
        let parallel_schedule = ParallelScheduleBuilder::build_from_rws(&mut mock_block(), 8);

        let mut sequential_schedule = ConcurrentSchedule::new();
        sequential_schedule.build_from_rws(&mut mock_block());

        assert_eq!(parallel_schedule, sequential_schedule);
    }
}