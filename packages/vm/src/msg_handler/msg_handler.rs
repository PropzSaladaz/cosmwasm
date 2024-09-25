use std::sync::{Arc, RwLock};

use crate::{
    symb_exec::{ProfileEvaluator, ProfileGenerator}, testing::{ConcurrentStorage, StorageWrapper}, vm_manager::{SCManager, VMManager}, vm_transactions::SerializableTransaction, BackendApi, BackendBuilder, CodeId, ConcurrentBackendBuilder, Querier, ReplayLogs, VMTransaction
};

#[derive(Debug)]
pub enum Message<'a> {
    Invocation(SerializableTransaction),
    Deployment {
        contract_code: &'a [u8],
        code_id: Option<CodeId>, // used for replay txs
    }
}

pub struct MessageHandler<A, S, W, Q, E> 
where
    A: BackendApi                           + 'static + Send + Sync,
    S: ConcurrentStorage                    + 'static + Send + Sync,
    W: StorageWrapper                       + 'static,
    Q: Querier                              + 'static + Send + Sync,
    E: ProfileGenerator + ProfileEvaluator  + 'static + Send + Sync,
{
    vm_manager: VMManager<A, S, W, Q, E>,
    sc_manager: Arc<RwLock<SCManager<A, S, W, Q, E>>>,
    block_size: usize,
}

impl<A, S, W, Q, E> MessageHandler<A, S, W, Q, E> 
where
    A: BackendApi                           + Send + Sync, 
    S: ConcurrentStorage                    + Send + Sync, 
    W: StorageWrapper,                  
    Q: Querier                              + Send + Sync,
    E: ProfileGenerator + ProfileEvaluator  + Send + Sync,
{

    pub fn new(
        sc_manager: Arc<RwLock<SCManager<A, S, W, Q, E>>>, 
        block_size: usize,

        backend_builder: Arc<BackendBuilder<A, S, Q>>,
        concurrent_backend_builder: Arc<ConcurrentBackendBuilder<A, S, W, Q>>, 
        n_threads: u16, 
        max_concurrent_instances: u16
    )-> Self {
        MessageHandler {
            vm_manager: VMManager::new(
                Arc::clone(&sc_manager), 
                backend_builder, 
                concurrent_backend_builder, 
                n_threads, 
                max_concurrent_instances
            ),
            block_size,
            sc_manager,
        }
    }

    pub fn handle_messages(&mut self, messages: Vec<Message>) {
        let mut invocations = vec![];
        let total_size = messages.len();
        for (idx, message) in messages.into_iter().enumerate() {
            match message {
                Message::Deployment { 
                    contract_code,
                    code_id 
                } => {
                    self.sc_manager.write().unwrap().save_code(contract_code, code_id).unwrap();
                },
                Message::Invocation (vm_message) => {
                    let vm_tx = VMTransaction {
                        transaction: vm_message.transaction,
                        replay_logs: ReplayLogs {
                            log_execute: vm_message.log_execute,
                            log_instantiate: vm_message.log_instantiate,
                            log_migrate: vm_message.log_migrate,
                            log_reply: vm_message.log_reply,
                        },
                    };

                    invocations.push(vm_tx);
                    
                    if (invocations.len() == self.block_size) || // can fill a block
                        idx == total_size - 1 { // reaches last tx
                        let resps = self.vm_manager.handle_block(invocations).unwrap();
                        invocations = vec![];
                        // resps.iter().for_each(|resp| println!("{:#?}", resp));
                    }
                }
            }
        }
    }
}


#[cfg(test)]
mod tests {

    #[test]
    fn handle_messages() {

    }
}
