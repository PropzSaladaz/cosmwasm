use cosmwasm_std::Addr;
use serde::{Deserialize, Serialize};

// INSTANTIATE -------------------------------------------
#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct InstantiateMsg {
}

// EXECUTE ------------------------------------------------
#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub enum ExecuteMsg {
    // simple state
    SimpleAddUser {
        user: String
    },
    SimpleAddOne {
        user: String
    },
    SimpleAddOneToADMIN {},

    // complex state
    ComplexExecute(ComplexBankExecute) 
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub enum ComplexBankExecute {
    CreateAcc {
        acc_name: String,
    },
    CreateSharedAcc {
        acc_name: String,
        owners: Vec<String>,
    },
    AddAdminToSharedAcc {
        acc_name: String,
        new_admin: String,
    },
    Deposit {
        acc_name: String,
        owner: String,
        amount: u128,
    },
    Transfer {
        acc_from: String,
        shared_owner: String,
        acc_to: String,
        amount: u128
    },


}


// QUERY --------------------------------------------------
#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub enum QueryMsg {
    // the curly braces allow for the serialzed json to be in the correct format!
    // https://book.cosmwasm.com/basics/query.html
    GetBalance {
        acc_name: String
    },
    GetComplexAccBalance {
        acc_name: String
    },
    GetAccDetails {
        acc_name: String
    },
    GetBankAnalytics {},
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct GetBalanceResp {
    pub balance: u64,
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct GetComplexBalanceResp {
    pub balance: u128,
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct AdminListResp {
    pub admins: Vec<Addr>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct GetAccDetails {
    pub ty: String,
    pub balance: u128,
    pub owners: Vec<String>
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct GetBankAnalytics {
    pub total_money: u128,
    pub total_users: u128,
    pub average_money_per_user: u128
}

