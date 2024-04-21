use crate::msg::{ExecuteMsg, InstantiateMsg, QueryMsg};
use cosmwasm_std::{
    to_json_binary, Binary, Deps, DepsMut, Empty, Env, MessageInfo, Response, StdResult, StdError
};
use crate::state::COINS;

// pub fn execute(
//     _deps: DepsMut,
//     _env: Env,
//     _info: MessageInfo,
//     _msg: ExecuteMsg,
// ) -> StdResult<Response> {
//     use ExecuteMsg::*;
//     match _msg {
//         AddUser { admin } => execute::add_user(_deps, _info, admin),
//         AddOne { } => execute::add(_deps),
//         Transfer {from , to} => Ok(Response::new()),
//     }
// }

pub fn instantiate(
    _deps: DepsMut,
    _env: Env,
    _info: MessageInfo,
    _msg: InstantiateMsg,
) -> StdResult<Response> {
    COINS.save(_deps.storage, "ADMIN".to_owned(), &1000)?;

    Ok(Response::new())
}

// pub fn query(
//     _deps: Deps, 
//     _env: Env, 
//     _msg: QueryMsg
// ) -> StdResult<Binary> {
//     use QueryMsg::*;

//     match _msg {
//         GetBalance {} => to_json_binary(&query::get_balance(_deps)?),
//     }
// }

mod execute {
    use super::*;
    use cosmwasm_std::{StdResult};

    pub fn add_user(deps: DepsMut, info: MessageInfo, user: String) -> StdResult<Response> {
        match COINS.may_load(deps.storage, user.clone()) {
            Ok(Some(_)) => return Err(StdError::generic_err("User already exists")),
            Ok(None) =>  COINS.save(deps.storage, user, &100)?,
            Err(e) => return Err(StdError::generic_err(format!("Error: {}", e))),
        }
        Ok(Response::new())
    }

    pub fn add(deps: DepsMut) -> StdResult<Response> {
        COINS.update(deps.storage, "ADMIN".to_owned(), |bank: Option<u64>| {
            match bank {
                Some(value) => Ok(value + 1),
                None => Err(StdError::generic_err("Value doesn't exist")),
            }
        })?;

        Ok(Response::new())

    }
}

mod query {
    use crate::msg::{GetBalanceResp};

    use super::*;

    pub fn get_balance(deps: Deps) -> StdResult<GetBalanceResp> {
        let balance = COINS.load(deps.storage, "ADMIN".to_owned()).unwrap();

        let resp = GetBalanceResp { balance };
        Ok(resp)
    }
}

#[cfg(test)]
mod tests {
    use crate::msg::AdminListResp;

    use super::*;
    use cosmwasm_std::Addr;
    use cw_multi_test::{App, ContractWrapper, Executor};


    #[test]
    fn greet_query() {
        // let mut app = App::default();

        // let code = ContractWrapper::new(execute, instantiate, query);
        // let code_id = app.store_code(Box::new(code));

        // let addr = app
        //     .instantiate_contract(
        //         code_id, 
        //         Addr::unchecked("owner"),
        //         &InstantiateMsg {
        //             admins: vec![
        //                 "admin1".to_string() , 
        //                 "admin2".to_string()
        //             ]
        //         },
        //         &[],
        //         "Contract",
        //         None
        //     ).unwrap();

        // let resp: GreetResp = app
        //     .wrap()
        //     .query_wasm_smart(addr, &QueryMsg::Greet {})
        //     .unwrap();

        // assert_eq!(
        //     resp,
        //     GreetResp {
        //         message: "Hello World".to_owned()
        //     }
        // )
    }

    #[test]
    fn instantiation() {
        // let mut app = App::default();

        // let code = ContractWrapper::new(execute, instantiate, query);
        // let code_id = app.store_code(Box::new(code));

        // let addr = app.instantiate_contract(
        //     code_id, 
        //     Addr::unchecked("owner"),
        //     &InstantiateMsg { 
        //         admins: vec!["admin1".to_owned()]
        //     }, 
        //     &[], 
        //     "contract 1",
        //     None
        // ).unwrap();

        // let resp: AdminListResp = app.wrap().query_wasm_smart(
        //     addr,
        //     &QueryMsg::AdminList {}
        // ).unwrap();

        // assert_eq!(
        //     resp, 
        //     AdminListResp { 
        //         admins: vec![Addr::unchecked("admin1")]
        //     }
        // );


    }

}