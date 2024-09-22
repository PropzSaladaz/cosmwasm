use std::sync::{Arc, RwLock};

use cosmwasm_std::Storage;
use crate::DepsMut;

use super::{evaluator::eval::SEContext, parser::{
    nodes::*, SCProfile
}, SCProfileParser};

pub trait SEEngineParse {
    fn parse_smart_contract(contract: &[u8]) -> SEProfile;
}

pub struct SEProfile {
    pub status: SEStatus,
    pub profile: String,
}

#[derive(Debug, Default, PartialEq, Eq,  Clone, Copy)]
pub enum SEStatus {
    #[default]
    Incomplete, // PathExplosion
    Complete, 
}

#[derive(Debug, Clone, Default)]
pub struct TxRWS {
    pub storage_dependency: StorageDependency,
    pub profile_status: SEStatus,
    pub rws_uid: String,
    pub rws: Vec<ReadWrite>
}

impl PartialEq for TxRWS {
    // do not consider the RWS hash
    fn eq(&self, other: &Self) -> bool {
        self.storage_dependency == other.storage_dependency &&
        self.profile_status == other.profile_status &&
        self.rws == other.rws
    }
}
pub trait ProfileGenerator {
    /// Generates the in-memory structure representing all possible paths captured by symbolic execution.
    /// This profile is static, meaning it never changes throughout execution, but it allows evaluation at runtime
    /// given some inputs, allowing to get the RWS from it
    fn generate_profile(&self, contract: &[u8]) -> SCProfile;
}

/// Parses the profile tree & gets the RWS for the wanted entry point 
/// given the message inputs as well as the current storage state
pub trait ProfileEvaluator {
    fn get_rws_instantiate<'a>(&self, sc_profile: &SCProfile, deps: &'a DepsMut<'a>, custom: &[u8]) -> TxRWS;
    fn get_rws_execute<'a>    (&self, sc_profile: &SCProfile, deps: &'a DepsMut<'a>, custom: &[u8]) -> TxRWS;
    fn get_rws_reply          (&self) -> TxRWS;
    fn get_rws_migrate        (&self) -> TxRWS;
    fn get_rws_ibc_init       (&self) -> TxRWS;
    fn get_rws_ibc_try        (&self) -> TxRWS;
    fn get_rws_ibc_ack        (&self) -> TxRWS;
    fn get_rws_ibc_confirm    (&self) -> TxRWS;
    fn get_rws_recv_packet    (&self) -> TxRWS;
    fn get_rws_timeout        (&self) -> TxRWS;
    fn get_rws_ack            (&self) -> TxRWS;
}


#[derive(Default)]
pub struct SymbolicExecutionEngine {}

impl SymbolicExecutionEngine {
    pub fn new() -> Self {
        Self::default()
    }
}

impl ProfileGenerator for SymbolicExecutionEngine {
    fn generate_profile(&self, _contract: &[u8]) -> SCProfile {

        // mock generation of SE output
        let symb_exec_profile = SEProfile {
            status: SEStatus::Complete,
            profile: r#"I ----------------------------

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
    - user: string
> SetVal:
    - user: string
    - val: int
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
=> GET(=AARiYW5r @ _msg.user): Inc
=> SET(=AARiYW5r @ _msg.user): Inc
<- [PC_4]

[PC_4] Type(_msg) == SetVal
=> GET(=AARiYW5r @ _msg.user): Non-Inc
=> SET(=AARiYW5r @ _msg.user): Non-Inc
<- [PC_5]

[PC_5] Type(_msg) == DoubleVal
=> GET(=AARiYW5r @ _msg.user): Non-Inc
=> SET(=AARiYW5r @ _msg.user): Non-Inc
<- [PC_6]

[PC_6] Type(_msg) == Transfer
=> None
<- None

Q ----------------------------

_deps: DepsMut
_env: Env
_msg: QueryMsg
> GetBalance:
    - user: string

[PC_1] True
=> GET(=AARiYW5r @ _msg.user): Non-Inc
<- None
"#
            .to_owned()
        };

        SCProfileParser::from_se_profile(symb_exec_profile)
    }
}

impl ProfileEvaluator for SymbolicExecutionEngine {

    fn get_rws_instantiate<'a>(&self, sc_profile: &SCProfile, deps: &'a DepsMut<'a>, custom: &[u8]) -> TxRWS {
        SymbolicExecutionEngine::get_rws(&EntryPoint::Instantiate, sc_profile, deps, custom)
    }

    fn get_rws_execute<'a>(&self, sc_profile: &SCProfile, deps: &'a DepsMut<'a>, custom: &[u8]) -> TxRWS {
        SymbolicExecutionEngine::get_rws(&EntryPoint::Execute, sc_profile, deps, custom)
    }
    
    fn get_rws_reply(&self) -> TxRWS {
        todo!()
    }
    
    fn get_rws_migrate(&self) -> TxRWS {
        todo!()
    }
    
    fn get_rws_ibc_init(&self) -> TxRWS {
        todo!()
    }
    
    fn get_rws_ibc_try(&self) -> TxRWS {
        todo!()
    }
    
    fn get_rws_ibc_ack(&self) -> TxRWS {
        todo!()
    }
    
    fn get_rws_ibc_confirm(&self) -> TxRWS {
        todo!()
    }
    
    fn get_rws_recv_packet(&self) -> TxRWS {
        todo!()
    }
    
    fn get_rws_timeout(&self) -> TxRWS {
        todo!()
    }
    
    fn get_rws_ack(&self) -> TxRWS {
        todo!()
    }
}

impl SymbolicExecutionEngine {

    /// Auxiliary method to get the root node of the profile for the specified entry point & parse it to retrieve the RWS
    fn get_rws<'b>(entry_point: &EntryPoint, sc_profile: &SCProfile, deps: &'b DepsMut<'b>, custom: &[u8]) -> TxRWS {
        let execute_entry_point = sc_profile.entry_point.get(&entry_point).unwrap();
        let path_cond = &execute_entry_point.root_path_cond.as_ref().unwrap();
        let arg_types = &execute_entry_point.inputs;

        let context = SEContext::new(custom, arg_types);
        let (storage_dependency, rws_uid, rws) = SymbolicExecutionEngine::parse_tree(path_cond, deps.storage, &context);

        TxRWS {
            storage_dependency,
            profile_status: sc_profile.status,
            rws_uid,
            rws,
        }
    }

    fn parse_tree(path_cond: &Arc<RwLock<Box<PathConditionNode>>> , storage: &dyn Storage, context: &SEContext ) -> 
        (StorageDependency, String, Vec<ReadWrite>) {

        match path_cond.write().unwrap().parse_tree(storage, &context) {
            PathConditionNode::RWSNode { 
                storage_dependency, 
                rws_uid,
                rws
            } => (
                storage_dependency,
                rws_uid,
                rws
            ),
            PathConditionNode::None => (StorageDependency::Independent, "".to_owned(), vec![]),
            other => unreachable!("Expecting RWSNode, got {:?}", other)
        }
    }
}



// ---------------------------------------------------------------
//                      MOCK
// ---------------------------------------------------------------

pub struct SEEngine {}

impl SEEngineParse for SEEngine {
    fn parse_smart_contract(_: &[u8]) -> SEProfile {
        SEProfile {
            status: SEStatus::Complete,
            profile: r#"I ----------------------------

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
    - user: string
> SetVal:
    - user: string
    - val: int
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
=> GET(=AARiYW5r @ _msg.user): Inc
=> SET(=AARiYW5r @ _msg.user): Inc
<- [PC_4]

[PC_4] Type(_msg) == SetVal
=> GET(=AARiYW5r @ _msg.user): Non-Inc
=> SET(=AARiYW5r @ _msg.user): Non-Inc
<- [PC_5]

[PC_5] Type(_msg) == DoubleVal
=> GET(=AARiYW5r @ _msg.user): Non-Inc
=> SET(=AARiYW5r @ _msg.user): Non-Inc
<- [PC_6]

[PC_6] Type(_msg) == Transfer
=> None
<- None

Q ----------------------------

_deps: DepsMut
_env: Env
_msg: QueryMsg
> GetBalance:
    - user: string

[PC_1] True
=> GET(=AARiYW5r @ _msg.user): Non-Inc
<- None
"#
            .to_owned()
        }
    }
}




#[cfg(test)]
mod tests {

    use crate::{symb_exec::se_engine::SEStatus, testing::{mock_env, mock_info, MockConcurrentStorage}, DepsMut, SCProfile, SCProfileParser};

    use super::{ProfileEvaluator, SymbolicExecutionEngine};


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

        let custom = br#"{
            "AddUser": {
                "admin": "SUIII"
            }
        }"#;

        let querier = cosmwasm_std::testing::MockQuerier::default();
        let mut_deps = DepsMut { 
            storage: &mut MockConcurrentStorage::default(),
            api: &cosmwasm_std::testing::MockApi::default(), 
            querier: cosmwasm_std::QuerierWrapper::new( &querier)
        };

        let engine = SymbolicExecutionEngine::default();

        let rws = engine.get_rws_execute(&contract, &mut_deps, custom);
    }
}