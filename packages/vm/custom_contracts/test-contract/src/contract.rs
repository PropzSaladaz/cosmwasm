use std::collections::HashMap;

use crate::{msg::{ComplexBankExecute, ExecuteMsg, InstantiateMsg, QueryMsg}, state::{Bank, BankAnalytics, BANK_ANALYTICS, COMPLEX_BANK}};
use cosmwasm_std::{
    to_json_binary, Binary, Deps, DepsMut, Empty, Env, MessageInfo, Response, StdResult, StdError
};
use crate::state::COINS;

const DEFAULT_BALANCE: u128 = 1000;

pub fn execute(
    _deps: DepsMut,
    _env: Env,
    _info: MessageInfo,
    _msg: ExecuteMsg,
) -> StdResult<Response> {
    use ExecuteMsg::*;
    use ComplexBankExecute::*;

    match _msg {
        // simple state
        SimpleAddUser { user } => execute::simple_add_user(_deps, _info, user),
        SimpleAddOne { user } => execute::simple_add(_deps, user),
        SimpleAddOneToADMIN {} => execute::simple_add(_deps, "ADMIN".to_owned()),

        // complex state
        ComplexExecute(complex) => match complex {
            CreateAcc { acc_name } 
                    => execute::complex_create_acc(_deps, _info, acc_name),
            CreateSharedAcc { acc_name, owners } 
                    => execute::complex_create_shared_acc(_deps, _info, acc_name, owners),
            AddAdminToSharedAcc { acc_name, new_admin }
                    => execute::complex_add_admin_shared_acc(_deps, _info, acc_name, new_admin),
            Deposit { acc_name, owner, amount } 
                    => execute::complex_deposit(_deps, _info, acc_name, owner, amount),
            Transfer { acc_from, shared_owner, acc_to, amount }
                    => execute::complex_transfer(_deps, _info, acc_from, shared_owner, acc_to, amount),
        }
    }
}

pub fn instantiate(
    _deps: DepsMut,
    _env: Env,
    _info: MessageInfo,
    _msg: InstantiateMsg,
) -> StdResult<Response> {
    // start with ADMIN with balance 1000
    COINS.save(_deps.storage, "ADMIN".to_owned(), &1000)?;

    COMPLEX_BANK.save(_deps.storage, &Bank {
        accounts: HashMap::new()
    })?;

    BANK_ANALYTICS.save(_deps.storage, &BankAnalytics {
        total_money: 0,
        total_users: 0,
        average_money_per_user: 0,
    })?;

    Ok(Response::new())
}

pub fn query(
    _deps: Deps, 
    _env: Env, 
    _msg: QueryMsg
) -> StdResult<Binary> {
    use QueryMsg::*;

    match _msg {
        GetBalance { acc_name } 
                => to_json_binary(&query::get_balance(_deps, acc_name)?),
        GetComplexAccBalance { acc_name } 
                => to_json_binary(&query::get_complex_balance(_deps, acc_name)?),
        GetAccDetails { acc_name }
                => to_json_binary(&query::get_complex_acc_details(_deps, acc_name)?),
        GetBankAnalytics { }
                => to_json_binary(&query::get_complex_bank_analytics(_deps)?),
    }
}

mod execute {
    use std::{cell::RefCell, rc::Rc};

    use crate::state::{Account, BankAnalytics, BANK_ANALYTICS, COMPLEX_BANK};

    use super::*;
    use cosmwasm_std::{Addr, StdResult};

    pub fn simple_add_user(deps: DepsMut, info: MessageInfo, user: String) -> StdResult<Response> {
        match COINS.may_load(deps.storage, user.clone()) {
            Ok(Some(_)) => return Err(StdError::generic_err("User already exists")),
            Ok(None) =>  COINS.save(deps.storage, user, &100)?,
            Err(e) => return Err(StdError::generic_err(format!("Error: {}", e))),
        }
        Ok(Response::new())
    }

    pub fn simple_add(deps: DepsMut, user: String) -> StdResult<Response> {
        COINS.update(deps.storage, user, |bank: Option<u64>| {
            match bank {
                Some(value) => Ok(value + 1),
                None => Err(StdError::generic_err("Value doesn't exist")),
            }
        })?;
        Ok(Response::new())
    }


    pub fn complex_create_acc(_deps: DepsMut, _info: MessageInfo, acc_name: String) -> StdResult<Response> {
        let mut bank = COMPLEX_BANK.load(_deps.storage)?;
        match bank.accounts.get(&acc_name) {
            Some(_) => Err(StdError::generic_err("Account already exists!")), 
            None => {
                let account = Account::OwnedAccount {
                    balance: DEFAULT_BALANCE,
                    owner: _info.sender
                };

                bank.accounts.insert(acc_name, account);
                COMPLEX_BANK.save(_deps.storage, &bank)?;

                update_bank_analytics_new_acc(_deps);

                Ok(Response::new())
            }
        }
    }

    pub fn complex_create_shared_acc(_deps: DepsMut, _info: MessageInfo, acc_name: String, owners: Vec<String>) -> StdResult<Response> {
        let mut bank = COMPLEX_BANK.load(_deps.storage)?;
        match bank.accounts.get(&acc_name) {
            Some(_) => Err(StdError::generic_err("Account already exists!")), 
            None => {
                let account = Account::SharedAccount {
                    balance: DEFAULT_BALANCE,
                    owners: owners,
                };

                bank.accounts.insert(acc_name, account);
                COMPLEX_BANK.save(_deps.storage, &bank)?;

                update_bank_analytics_new_acc(_deps);

                Ok(Response::new())
            }
        }
    }

    pub fn complex_add_admin_shared_acc(_deps: DepsMut, _info: MessageInfo, acc_name: String, admin: String) -> StdResult<Response> {
        let mut bank = COMPLEX_BANK.load(_deps.storage)?;
        match bank.accounts.get_mut(&acc_name) {
            Some(acc) => {
                match acc {
                    Account::SharedAccount { balance: _, owners } => {               
                        owners.push(admin);
                        COMPLEX_BANK.save(_deps.storage, &bank)?;      
                        Ok(Response::new())
                    },
                    Account::OwnedAccount { balance: _, owner: _ } => Err(StdError::generic_err("Account type is not SharedAccount!")),

                }
            },
            None => Err(StdError::generic_err("Account doesn't exist!")),  
        }
    }

    pub fn complex_deposit(_deps: DepsMut, _info: MessageInfo, acc_name: String, owner: String, amount: u128) -> StdResult<Response> {
        let mut bank = COMPLEX_BANK.load(_deps.storage)?;
        match bank.accounts.get_mut(&acc_name) {
            Some(acc) => {
                match acc {
                    Account::SharedAccount { balance, owners } => {     
                        if owners.iter().any(|o| o == owner.as_str()) {
                            *balance = *balance + amount;
                            COMPLEX_BANK.save(_deps.storage, &bank)?;
                            update_bank_analytics_deposit(_deps, amount);
                            Ok(Response::new())
                        }
                        else {
                            Err(StdError::generic_err("sender is not owner of shared acc"))
                        }

                    },
                    Account::OwnedAccount { balance, owner } => {
                        if _info.sender == *owner {
                            *balance = *balance + amount;
                            COMPLEX_BANK.save(_deps.storage, &bank)?;
                            update_bank_analytics_deposit(_deps, amount);
                            Ok(Response::new())
                        }
                        else {
                            Err(StdError::generic_err("sender is not owner of owned acc"))
                        }
                    },

                }
            },
            None => Err(StdError::generic_err("Account doesn't exist!")),  
        }
    }

    pub fn complex_transfer(_deps: DepsMut, _info: MessageInfo, 
            acc_from: String, owner: String, acc_to: String, amount: u128) -> StdResult<Response> {

        let mut bank = COMPLEX_BANK.load(_deps.storage)?;

        // check if account exists
        match &bank.accounts.get(&acc_from) {
            None => return Err(StdError::generic_err("acc_from doesnt exist")),
            // check acc balance
            Some(acc) => match acc {
                Account::SharedAccount { balance, owners: _ } |
                Account::OwnedAccount { balance, owner: _ } => if *balance < amount {
                    return Err(StdError::generic_err("sender does not have enough funds"))
                }
                
            }
        }

        match &bank.accounts.get(&acc_to)  {
            None => return Err(StdError::generic_err("acc_to doesnt exist")),
            _ => ()
        }

        // check if sender is authorized
        match &bank.accounts.get_mut(&acc_from).unwrap() {
            Account::SharedAccount { balance: _, owners } => {     
                if !owners.iter().any(|o| o == owner.as_str()) {
                    return Err(StdError::generic_err("sender is not owner of shared acc"))
                }
            },
            Account::OwnedAccount { balance: _, owner } => {
                if _info.sender != *owner {
                    return Err(StdError::generic_err("sender is not owner of owned acc"))
                }
            },
        };

        let sender_acc = bank.accounts.get_mut(&acc_from).unwrap();
        match sender_acc {
            Account::SharedAccount { balance, owners: _ } |
            Account::OwnedAccount { balance, owner: _ }
            => *balance = *balance - amount,
        }

        let dest_acc = bank.accounts.get_mut(&acc_to).unwrap();
        match dest_acc {
            Account::SharedAccount { balance, owners: _ } |
            Account::OwnedAccount { balance, owner: _ }
            => *balance = *balance + amount,
        }

        COMPLEX_BANK.save(_deps.storage, &bank)?;
        Ok(Response::new()) 
        

    }


    fn update_bank_analytics_new_acc(_deps: DepsMut) {
        update_bank_analytics(_deps, DEFAULT_BALANCE, 1);
    }

    fn update_bank_analytics_deposit(_deps: DepsMut, amount: u128) {
        update_bank_analytics(_deps, amount, 0);
    }

    fn update_bank_analytics(_deps: DepsMut, amount: u128, new_users: u128) {
        BANK_ANALYTICS.update(_deps.storage, move |analytics| -> StdResult<_> {
            let mut new_analytics = BankAnalytics {
                total_money: analytics.total_money,
                total_users: analytics.total_users,
                average_money_per_user: analytics.average_money_per_user,
            };
            new_analytics.total_money += amount;
            new_analytics.total_users += new_users;
            new_analytics.average_money_per_user = new_analytics.total_money / new_analytics.total_users;
            Ok(new_analytics)
        }).unwrap();
    }
}

mod query {
    use crate::{msg::{GetAccDetails, GetBalanceResp, GetBankAnalytics, GetComplexBalanceResp}, state::Account};

    use super::*;

    pub fn get_balance(deps: Deps, acc_name: String) -> StdResult<GetBalanceResp> {
        let balance = COINS.load(deps.storage, acc_name).unwrap();

        let resp = GetBalanceResp { balance };
        Ok(resp)
    }

    pub fn get_complex_balance(deps: Deps, acc_name: String) -> StdResult<GetComplexBalanceResp> {
        let bank = COMPLEX_BANK.load(deps.storage)?;
        match bank.accounts.get(&acc_name) {
            Some(acc) => match acc {
                Account::OwnedAccount { balance, owner: _ } |
                Account::SharedAccount { balance, owners: _ } => {
                    let resp = GetComplexBalanceResp { balance: *balance };
                    Ok(resp)
                }
            },
            None => Err(StdError::generic_err("Acc doesn't exist"))
        }
    }

    pub fn get_complex_acc_details(deps: Deps, acc_name: String) -> StdResult<GetAccDetails> {
        let bank = COMPLEX_BANK.load(deps.storage)?;
        match bank.accounts.get(&acc_name) {
            Some(acc) => match acc {
                Account::OwnedAccount { balance, owner } => {
                    let resp = GetAccDetails { 
                        ty: "OwnedAcc".to_owned(), 
                        balance: *balance,
                        owners: vec![(*owner).as_str().to_owned()]
                    };
                    Ok(resp)
                }
                Account::SharedAccount { balance, owners } => {
                    let resp = GetAccDetails { 
                        ty: "SharedAcc".to_owned(), 
                        balance: *balance,
                        owners: (*owners).clone()
                    };
                    Ok(resp)
                }
            },
            None => Err(StdError::generic_err("Acc doesn't exist"))
        }
    }

    pub fn get_complex_bank_analytics(deps: Deps) -> StdResult<GetBankAnalytics> {
        let analytics = BANK_ANALYTICS.load(deps.storage)?;
        let resp = GetBankAnalytics {
            total_money: analytics.total_money,
            total_users: analytics.total_users,
            average_money_per_user: analytics.average_money_per_user,
        };
        Ok(resp)
    }

}