pub trait SEEngineParse {
    fn parse_smart_contract(contract: &[u8]) -> SEProfile;
}

pub struct SEProfile {
    pub status: SEStatus,
    pub profile: String,
}

#[derive(Debug, PartialEq, Eq,  Clone, Copy)]
pub enum SEStatus {
    Incomplete, // PathExplosion
    Complete, 
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
<- None"#
            .to_owned()
        }
    }
}