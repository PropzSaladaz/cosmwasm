use cosmwasm_std::Addr;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct InstantiateMsg {
}

// EXECUTE ------------------------------------------------
#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub enum ExecuteMsg {
    AddUser {
        admin: String
    },
    AddOne {
        user: String,
    },
    SetVal { 
        user: String,
        val: u64 
    },
    DoubleVal { 
        user: String,
    },
    Transfer {
        from: String,
        to: String
    }
}


// QUERY --------------------------------------------------
#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub enum QueryMsg {
    // the curly braces allow for the serialzed json to be in the correct format!
    // https://book.cosmwasm.com/basics/query.html
    GetBalance { 
        user: String,
    },
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct GetBalanceResp {
    pub balance: i64,
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct AdminListResp {
    pub admins: Vec<Addr>,
}