use std::sync::{Arc, RwLock};

use crate::{testing::{ConcurrentStorage, StorageWrapper}, vm_manager::{SCManager, VMManager, VMMessage}, BackendApi, Querier, Storage};

pub enum Message<'a> {
    Invocation(VMMessage),
    Deployment {
        contract_code: &'a [u8],
    }
}

pub struct MessageHandler<A, S, W, Q> 
where
    A: BackendApi        + 'static + Send + Sync,
    S: ConcurrentStorage + 'static + Send + Sync,
    W: StorageWrapper    + 'static,
    Q: Querier           + 'static + Send + Sync,
{
    vm_manager: VMManager<A, S, W, Q>,
    sc_manager: Arc<RwLock<SCManager<A, S, W, Q>>>,
    block_size: usize,
}

impl<A, S, W, Q> MessageHandler<A, S, W, Q> 
where
    A: BackendApi        + Send + Sync, 
    S: ConcurrentStorage + Send + Sync, 
    W: StorageWrapper,
    Q: Querier           + Send + Sync
{

    pub fn new(sc_manager: Arc<RwLock<SCManager<A, S, W, Q>>>, vm_manager: VMManager<A, S, W, Q> , block_size: usize)-> Self {
        MessageHandler {
            vm_manager,
            sc_manager,
            block_size,
        }
    }

    pub fn handle_messages(&mut self, messages: Vec<Message>) {
        let mut invocations = vec![];
        let total_size = messages.len();
        for (idx, message) in messages.into_iter().enumerate() {
            match message {
                Message::Deployment { contract_code } => {
                    self.sc_manager.write().unwrap().save_code(contract_code).unwrap();
                },
                Message::Invocation (vm_message) => {
                    invocations.push(vm_message);
                    
                    if (invocations.len() == self.block_size) || // can fill a block
                        idx == total_size - 1 { // reaches last tx
                        self.vm_manager.handle_block(invocations).unwrap();
                        invocations = vec![];
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
