use cosmwasm_std::{Addr, Decimal};
use cw_storage_plus::Map;

pub const COINS: Item<u64> = Item::new("bank");