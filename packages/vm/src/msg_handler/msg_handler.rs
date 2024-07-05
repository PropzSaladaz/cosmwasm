use std::sync::{Arc, RwLock};

use crate::{testing::ConcurrentStorage, vm_manager::{SCManager, VMManager, VMMessage}, BackendApi, Querier, Storage};

const BLOCK_SIZE: usize = 1;

pub enum Message<'a> {
    Invocation(VMMessage),
    Deployment {
        contract_code: &'a [u8],
    }
}

pub struct MessageHandler<A, S, Q> 
where
    A: BackendApi + 'static + Send + Sync,
    S: ConcurrentStorage + 'static + Send + Sync,
    Q: Querier + 'static + Send + Sync,
{
    vm_manager: VMManager<A, S, Q>,
    sc_manager: Arc<RwLock<SCManager<A, S, Q>>>,
}

impl<A, S, Q> MessageHandler<A, S, Q> 
where
    A: BackendApi + Send + Sync, 
    S: ConcurrentStorage + Send + Sync, 
    Q: Querier + Send + Sync
{

    pub fn new(sc_manager: Arc<RwLock<SCManager<A, S, Q>>>, vm_manager: VMManager<A, S, Q> )-> Self {
        MessageHandler {
            vm_manager,
            sc_manager
        }
    }

    pub fn handle_messages(&mut self, messages: Vec<Message>) {
        let mut invocations = vec![];
        for message in messages {
            match message {
                Message::Deployment { contract_code } => {
                    println!("deployment");
                    self.sc_manager.write().unwrap().save_code(contract_code).unwrap();
                },
                Message::Invocation (vm_message) => {
                    println!("invocation - 0");
                    invocations.push(vm_message);
                    println!("invocation - 1");
                    if invocations.len() == BLOCK_SIZE {
                        println!("handling block");
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
