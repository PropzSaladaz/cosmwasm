use cosmwasm_std::{Addr, Decimal};
use cw_storage_plus::Map;

pub const COINS: Map<String, i64> = Map::new("bank");