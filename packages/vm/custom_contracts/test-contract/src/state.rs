use std::collections::HashMap;

use cosmwasm_std::{Addr, Decimal};
use cw_storage_plus::{Item, Map};
use serde::{Deserialize, Serialize};



// simple state
pub const COINS: Map<String, u64> = Map::new("bank");



// fairly complex state

#[derive(Serialize, Deserialize)]
pub struct BankAnalytics {
    pub total_money: u128,
    pub total_users: u128,
    pub average_money_per_user: u128,
}

pub const BANK_ANALYTICS: Item<BankAnalytics> = Item::new("analytics");



// "very" complex state

#[derive(Serialize, Deserialize)]
pub enum Account {
    OwnedAccount {
        balance: u128,
        owner: Addr,
    },
    SharedAccount {
        balance: u128,
        owners: Vec<String>
    }
}

#[derive(Serialize, Deserialize)]
pub struct Bank {
    pub accounts: HashMap<String, Account>
}

pub const COMPLEX_BANK: Item<Bank> = Item::new("complex-bank");
