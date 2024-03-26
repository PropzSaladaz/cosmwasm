use cosmwasm_std::{Addr, Decimal};
use cw_storage_plus::Map;

pub const COINS: Map<String, u64> = Map::new("bank");