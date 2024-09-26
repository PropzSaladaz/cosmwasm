use std::sync::atomic::{AtomicUsize, Ordering};

use crate::symb_exec::{Commutativity, Key, ProfileEvaluator, ProfileGenerator, StorageDependency, TxRWS};
use crate::vm_transactions::OperationType;
use crate::{ReadWrite, SCProfile, SEStatus};

pub struct PerfectRWSEngine {
    rws_idx: AtomicUsize,
    rws_per_tx: Vec<TxRWS>,
}

impl ProfileGenerator for PerfectRWSEngine {
    // wont use the code for anything. Th eprofile swill serve no use
    fn generate_profile(&self, contract: &[u8]) -> SCProfile {
        SCProfile::default()
    }
}

impl ProfileEvaluator for PerfectRWSEngine {
    fn get_rws_instantiate<'a>(&self, sc_profile: &SCProfile, deps: &'a crate::DepsMut<'a>, custom: &[u8]) -> TxRWS {
        self.get_next_rws()
    }

    fn get_rws_execute<'a>    (&self, sc_profile: &SCProfile, deps: &'a crate::DepsMut<'a>, custom: &[u8]) -> TxRWS {
        self.get_next_rws()
    }
    
    fn get_rws_reply(&self) -> TxRWS {
        self.get_next_rws()
    }
    
    fn get_rws_migrate(&self) -> TxRWS {
        self.get_next_rws()
    }
    
    fn get_rws_ibc_init(&self) -> TxRWS {
        self.get_next_rws()
    }
    
    fn get_rws_ibc_try(&self) -> TxRWS {
        self.get_next_rws()
    }
    
    fn get_rws_ibc_ack(&self) -> TxRWS {
        self.get_next_rws()
    }
    
    fn get_rws_ibc_confirm(&self) -> TxRWS {
        self.get_next_rws()
    }
    
    fn get_rws_recv_packet(&self) -> TxRWS {
        self.get_next_rws()
    }
    
    fn get_rws_timeout(&self) -> TxRWS {
        self.get_next_rws()
    }
    
    fn get_rws_ack(&self) -> TxRWS {
        self.get_next_rws()
    }
}

impl PerfectRWSEngine {
    fn get_next_rws(&self) -> TxRWS {
        let old = self.rws_idx.load(Ordering::SeqCst);
        let res = self.rws_per_tx[old].clone();
        self.rws_idx.store(old + 1, Ordering::SeqCst);
        res
    }
}

impl PerfectRWSEngine {
    pub fn new(rws_per_tx: Vec<Vec<OperationType>>) -> Self {
        use OperationType::*;

        let mut rws_id = 0;
        let mut rws = Vec::with_capacity(rws_per_tx.len());

        for transaction in rws_per_tx {
            let mut operations = vec![];

            for operation in transaction {
                rws_id += 1;
                let operation = match operation {
                    Read(key) => {
                        ReadWrite::Read { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key.as_bytes().to_owned()), 
                            commutativity: Commutativity::NonCommutative, 
                            operation_node: None, 
                        }
                    },
                    Write(key) => {
                        ReadWrite::Write { 
                            storage_dependency: StorageDependency::Independent, 
                            key: Key::Bytes(key.as_bytes().to_owned()), 
                            commutativity: Commutativity::NonCommutative, 
                            operation_node: None, 
                        }
                    }
                };

                operations.push(operation);
            }

            let tx_rws = TxRWS {
                storage_dependency: StorageDependency::Independent,
                profile_status: SEStatus::Complete,
                rws_uid: rws_id.to_string(),
                rws: operations 
            };

            rws.push(tx_rws)
        }

        PerfectRWSEngine { 
            rws_idx: AtomicUsize::new(0),
            rws_per_tx: rws, 
        }
    }

    
}