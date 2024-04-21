use std::collections::HashMap;

use cosmwasm_std::Storage;

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
            "AddUser": {
                "admin": "name1",
                "balance": 2,
                "fee": 2.543,
                "neg": -5,
                "InternalObj": {
                    "field1": "still works"
                }
            }
        }"#, 
        arg_types,
        CosmwasmInputs::Mock
    )
}

pub struct MockStorage {
    storage: HashMap<Vec<u8>, Vec<u8>>,
}

impl Storage for MockStorage {
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        match self.storage.get(&key[..]) {
            Some(bytes) => Some(bytes.to_vec()),
            None => None,
        }
    }
    
    fn range<'a>(
        &'a self,
        start: Option<&[u8]>,
        end: Option<&[u8]>,
        order: cosmwasm_std::Order,
    ) -> Box<dyn Iterator<Item = cosmwasm_std::Record> + 'a> {
        todo!()
    }
    
    fn set(&mut self, key: &[u8], value: &[u8]) {
        todo!()
    }
    
    fn remove(&mut self, key: &[u8]) {
        todo!()
    }

}

pub fn mock_storage(storage: HashMap<Vec<u8>, Vec<u8>>) -> impl Storage
{
    MockStorage { storage }
}