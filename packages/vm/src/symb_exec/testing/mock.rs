use std::collections::HashMap;

use super::super::parser::nodes::*;
use super::super::evaluator::eval::*;

pub fn mock_arg_types() -> ArgTypes {
    ArgTypes::from([
        ("deps".to_owned(), InputType::DepsMut),
        ("env".to_owned(),  InputType::Env),
        ("info".to_owned(), InputType::MessageInfo),
        ("msg".to_owned(),  InputType::Custom)
    ])
}

pub fn mock_context(arg_types: &ArgTypes) -> SEContext {
    SEContext::new(br#"
        {
            "Adduser": {
                "admin": "name1",
                "balance": 2,
                "fee": 2.543,
                "neg": -5,
                "InternalObj": {
                    "field1": "still works"
                }
            }
        }"#, 
        arg_types
    )
}

pub struct MockStorage {
    storage: HashMap<Vec<u8>, Vec<u8>>,
}

impl StorageAccessor for MockStorage {
    fn get(&self, key: &Vec<u8>) -> Option<Vec<u8>> {
        match self.storage.get(&key[..]) {
            Some(bytes) => Some(bytes.to_vec()),
            None => None,
        }
    }
}

pub fn mock_storage(storage: HashMap<Vec<u8>, Vec<u8>>) -> impl StorageAccessor
{
    MockStorage { storage }
}