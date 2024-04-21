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
    AddOne {},
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
    GetBalance {},
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct GetBalanceResp {
    pub balance: u64,
}

#[derive(Serialize, Deserialize, PartialEq, Debug, Clone)]
pub struct AdminListResp {
    pub admins: Vec<Addr>,
}