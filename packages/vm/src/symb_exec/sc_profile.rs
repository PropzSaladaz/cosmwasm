use std::{cell::RefCell, rc::Rc};

use cosmwasm_std::{Env, MessageInfo, Storage};
use crate::{testing::MockStoragePartitioned, DepsMut};

use super::{evaluator::eval::SEContext, parser::{
    nodes::*, SCProfile
}, SEStatus};

#[derive(Debug, PartialEq)]
pub struct TxRWS {
    pub profile_status: SEStatus,
    pub rws: Vec<ReadWrite>
}

impl SCProfile {

    pub fn get_rws_instantiate<'a>(&self, deps: &'a DepsMut<'a>, env: &'a Env, msg_info: &'a MessageInfo, custom: &[u8]) -> TxRWS {
        self.get_rws_entry_point(
            CosmwasmInputs::Instantiate { 
                deps: deps, 
                env:  env, 
                info: msg_info 
            }, 
            &EntryPoint::Instantiate,
            custom
        )
    }

    pub fn get_rws_execute<'a>(&self, deps: &'a DepsMut<'a>, env: &'a Env, msg_info: &'a MessageInfo, custom: &[u8]) -> TxRWS {
        self.get_rws_entry_point(
            CosmwasmInputs::Execute { 
                deps: deps, 
                env:  env, 
                info: msg_info 
            }, 
            &EntryPoint::Execute,
            custom
        )
    }

    pub fn get_rws_query<'a>(&self, deps: &'a DepsMut<'a>, env: &'a Env, msg_info: &'a MessageInfo, custom: &[u8]) -> TxRWS {
        todo!();
    }

    /// Auxiliary method to map entry point to root path_cond_node & parse the corresponding tree, returning the RWS
    fn get_rws_entry_point<'b>(&self, cosmwasm_inputs: CosmwasmInputs<'b>, entry_point: &EntryPoint, custom: &[u8]) -> TxRWS {
        let execute_entry_point = self.entry_point.get(&entry_point).unwrap();
        let arg_types = &execute_entry_point.inputs;

        match &execute_entry_point.root_path_cond {
            Some(path_cond) => {
                match cosmwasm_inputs {
                    CosmwasmInputs::Execute     { deps, env: _, info: _ } => {
                        let context = SEContext::new(custom, arg_types, cosmwasm_inputs);
                        TxRWS {
                            profile_status: self.status,
                            rws: self.parse_tree(path_cond, deps.storage, &context)
                        }
                    },
                    CosmwasmInputs::Instantiate { deps: _, env: _, info: _ } => 
                    {
                        let context = SEContext::new(custom, arg_types, cosmwasm_inputs);
                        // TODO we are sending empty storage for instatiates -> Instantiates should not have yet a storage (the tx wasn't executed yet)
                        // thus we send a mock storage. Need to think better about this
                        TxRWS {
                            profile_status: self.status,
                            rws: self.parse_tree(path_cond, &MockStoragePartitioned::default(), &context)
                        }
                    }

                    _ => todo!()
                }
                
            },
            None => unreachable!()
        }
    }

    fn parse_tree(&self, path_cond: &Rc<RefCell<Box<PathConditionNode>>> , storage: &dyn Storage, context: &SEContext ) -> Vec<ReadWrite> {
        match path_cond.borrow_mut().parse_tree(storage, &context) {
            PathConditionNode::RWSNode(rws) => rws,
            PathConditionNode::None => vec![],
            other => unreachable!("Expecting RWSNode, got {:?}", other)
        }
    }

}

#[cfg(test)]
mod tests {

    use crate::{symb_exec::se_engine::SEStatus, testing::{mock_env, mock_info, MockStoragePartitioned}, DepsMut, SCProfile, SCProfileParser};


    fn build_contract() -> SCProfile {
        let s = r#"I ----------------------------

_deps: DepsMut
_env: Env
_info: MessageInfo
_msg: InstantiateMsg


[PC_1] True
=> SET(=AARiYW5rQURNSU4=): Non-Inc
<- None

E ----------------------------

_deps: DepsMut
_env: Env
_info: MessageInfo
_msg: ExecuteMsg
> AddUser:
    - admin: string
> AddOne:
> Transfer:
    - from: string
    - to: string


[PC_1] Type(_msg) == AddUser
=> [PC_2]
<- [PC_3]

[PC_2] GET(=AARiYW5r @ _msg.admin) == null
=> GET(=AARiYW5r @ _msg.admin): Non-Inc
=> SET(=AARiYW5r @ _msg.admin): Non-Inc
<- None

[PC_3] Type(_msg) == AddOne
=> GET(=AARiYW5rQURNSU4=): Inc
=> SET(=AARiYW5rQURNSU4=): Inc
<- [PC_4]

[PC_4] Type(_msg) == Transfer
=> None
<- None"#;

        SCProfileParser::from_string(SEStatus::Complete, s.to_owned())
    }
    
    #[test]
    fn get_rws_execute() {
        let contract = build_contract();
        let env = mock_env();
        let msg_info = mock_info("drake", &[]);

        let custom = br#"{
            "AddUser": {
                "admin": "SUIII"
            }
        }"#;

        let querier = cosmwasm_std::testing::MockQuerier::default();
        let mut_deps = DepsMut { 
            storage: &mut MockStoragePartitioned::default(),
            api: &cosmwasm_std::testing::MockApi::default(), 
            querier: cosmwasm_std::QuerierWrapper::new( &querier)
        };
        let rws = contract.get_rws_execute(&mut_deps, &env, &msg_info, custom);
        println!("RWS: {:#?}", rws);
    }
}