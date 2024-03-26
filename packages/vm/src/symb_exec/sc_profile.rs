use std::{borrow::Borrow, cell::RefCell, collections::HashMap, ops, rc::Rc};

use cosmwasm_std::{DepsMut, Env, MessageInfo};
use super::parser::{
    sc_profile_parser::SCProfile, 
    nodes::*
};
use serde_json::Value;

impl PathConditionNode {
    // fn parse_tree<T>(&self, f: T) -> &PathConditionNode
    // where T: Fn(Rule) 
    // {
    //     match &self {
    //         Self::ConditionNode { 
    //             condition, 
    //             pos_branch, 
    //             neg_branch 
    //         } => {
    //             // TODO - app_closure is hardcoded.. we need to pass this 
    //             if condition.as_ref().eval(|key: Key| &[0x12]) {
    //                 pos_branch.unwrap().as_ref().borrow().parse_tree(f)
    //             }
    //             else {
    //                 neg_branch.unwrap().as_ref().borrow().parse_tree(f)
    //             }
    //         },
    //         _ => self,
    //     }
    // }
}

impl SCProfile {

    pub fn get_rws_instantiate(&self, deps: DepsMut, env: Env, msg_info: MessageInfo, custom: &[u8]) {
        let profile = self.entry_point.get(&EntryPoint::Instantiate).unwrap();
        let root: &Rc<RefCell<Box<PathConditionNode>>> = profile.root_path_cond.as_ref().unwrap().borrow();
    }

    pub fn get_rws_execute(&self, deps: DepsMut, env: Env, msg_info: MessageInfo, custom: &[u8]) {
        let value: Value = serde_json::from_slice(custom).expect("Failed to deserialize execute message");
    }

    pub fn get_rws_query(&self, deps: DepsMut, env: Env, msg_info: MessageInfo, custom: &[u8]) {
        // TODO
    }

}