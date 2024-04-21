use std::{borrow::Borrow, cell::RefCell, rc::Rc};

use cosmwasm_std::{DepsMut, Env, MessageInfo};
use super::{evaluator::{eval::SEContext, path_cond}, parser::{
    nodes::*, SCProfile
}};
use serde_json::{de::Read, Value};

impl SCProfile {

    pub fn get_rws_instantiate<'a>(&self, deps: &'a DepsMut<'a>, env: &'a Env, msg_info: &'a MessageInfo, custom: &[u8]) -> Vec<ReadWrite> {
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

    pub fn get_rws_execute<'a>(&self, deps: &'a DepsMut<'a>, env: &'a Env, msg_info: &'a MessageInfo, custom: &[u8]) -> Vec<ReadWrite> {
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

    pub fn get_rws_query(&self, deps: DepsMut, env: Env, msg_info: MessageInfo, custom: &[u8]) -> Vec<ReadWrite> {
        todo!();
    }

    /// Auxiliary method to map entry point to root path_cond_node & parse the corresponding tree, returning the RWS
    fn get_rws_entry_point<'b>(&self, cosmwasm_inputs: CosmwasmInputs<'b>, entry_point: &EntryPoint, custom: &[u8]) -> Vec<ReadWrite> {
        let execute_entry_point = self.entry_point.get(&entry_point).unwrap();
        let arg_types = &execute_entry_point.inputs;

        match &execute_entry_point.root_path_cond {
            Some(path_cond) => {
                match cosmwasm_inputs {
                    CosmwasmInputs::Execute     { deps, env: _, info: _ } |
                    CosmwasmInputs::Instantiate { deps, env: _, info: _ } => 
                    {
                        let context = SEContext::new(custom, arg_types, cosmwasm_inputs);
                        match path_cond.as_ref().borrow().parse_tree(deps.storage, &context) {
                            PathConditionNode::RWSNode(rws) => rws,
                            other => unreachable!("Expecting RWSNode, got {:?}", other)
                        }
                    }

                    _ => todo!()
                }
                
            },
            None => unreachable!()
        }
    }

}

#[cfg(test)]
mod tests {
    use cosmwasm_std::{testing::mock_dependencies, DepsMut};

    use crate::{symb_exec::testing::mock::mock_storage, testing::{mock_backend, mock_env, mock_info}, SCProfile, SCProfileParser};


    fn build_contract() -> SCProfile {
        let s = r#"I ----------------------------

_deps: DepsMut
_env: Env
_info: MessageInfo
_msg: InstantiateMsg


[PC_1] True
=> SET(=AARiYW5rQURNSU4=): 1000
<- None

E ----------------------------

_deps: DepsMut
_env: Env
_info: MessageInfo
_msg: ExecuteMsg
> AddUser:
    - admin: stringg
> AddOne:
> Transfer:
    - from: string
    - to: string


[PC_1] Type(_msg) == AddUser
=> [PC_2]
<- [PC_3]

[PC_2] GET(=AARiYW5r @ _msg.admin) == null
=> SET(=AARiYW5r @ _msg.admin): 100
=> GET(=AARiYW5r @ _msg.admin)
<- None

[PC_3] Type(_msg) == AddOne
=> SET(=AARiYW5rQURNSU4=): GET(=AARiYW5rQURNSU4=) + 1
=> GET(=AARiYW5rQURNSU4=)
<- [PC_4]

[PC_4] Type(_msg) == Transfer
=> None
<- None"#;

        SCProfileParser::from_string(s.to_owned())
    }
    
    #[test]
    fn get_rws_execute() {
        // let contract = build_contract();
        // let deps mock_dependencies();
        // let env = mock_env();
        // let msg_info = mock_info("drake", &[]);

        // let custom = br#"{
        //     "AddUser": {}
        // }"#;

        // contract.get_rws_execute(deps, &env, &msg_info, custom);
    }
}