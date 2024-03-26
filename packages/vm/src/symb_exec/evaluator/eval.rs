use serde_json::{Value};

use crate::symb_exec::parser::nodes::{Expr, Identifier, Integer, Number};

use super::super::parser::nodes::Key;

/// Serves as reference context for attribute accessors in SE-output.
/// 
/// Whenever there is an indentifier - ```var1``` or ```var1.field1```, we look
/// into all fields of SEContext to find a match, and get the corresponding
/// primitive type
pub struct SEContext {
    pub custom_msg: Value,
    // TODO - need a way to also store the cosmwasm input types for each entry point
}

/// Used for expression evaluation - either using arithmetic or logical 
/// operations
pub trait Eval {
    /// Evaluation output type
    type Output;
    /// Binary operation's operand type
    type Operand;
    /// Binary operation's operator type
    type Operator;
    /// Binary operation's output type
    type OpOut;

    /// Takes an input closure to which we send the Key of the storage read (if any),
    /// and we get the bytes representing its value
    fn eval<F: Fn(Vec<u8>) -> Vec<u8> + Clone>(self, app_closure: &F, variable_context: &SEContext) -> Self::Output;
    fn op(lhs: Self::Operand, op: Self::Operator, rhs: Self::Operand) -> Self::OpOut;
    
    /// Parses a Key into bytes.
    /// 
    /// Uses the ```app_closure``` to get the actual value bytes given the key bytes.
    /// Currently converts all data to Int type - TODO
    fn eval_storage_read<F>(&self, key: Key, app_closure: &F, variable_context: &SEContext) -> Expr 
    where F: Fn(Vec<u8>) -> Vec<u8> + Clone
    {
        let mut bytes: Vec<u8>;
        match key {
            Key::Bytes(key) => bytes = app_closure(key),
            Key::Expression { base, expr } => {
                bytes = base;
                match expr.eval(&app_closure, &variable_context) {
                    Expr::Number(val) => match val {
                        Number::Float(f) => bytes.append(&mut f.to_le_bytes().to_vec()),
                        Number::Int(i)   => bytes.append(&mut i.to_le_bytes().to_vec())
                    },
                    Expr::Identifier(id) => bytes.append(&mut self.parse_identifier(id, variable_context)),
                    r => unreachable!("Expected ") 
                };
            }
        };
        Expr::Number(Number::Int(Integer::from_be_bytes(bytes.try_into().unwrap())))
    }

    /// Converts an identifier to the respective primitive type.
    /// This convertion is based on the received custom message, as well as on the
    /// Cosmwasm context types
    /// TODO - we are currently only checking attr accessors in the custom msg
    fn parse_identifier(&self, id: Identifier, variable_context: &SEContext) -> Vec<u8> {
        match id {
            // Run over the custom msg JSON map to get the value
            Identifier::AttrAccessor(attrs) => {
                let mut val = match &variable_context.custom_msg {
                    Value::Object(map) => map.get(attrs.get(0).unwrap()),
                    r => unreachable!("Expecting Value::Object, got {}", r),
                };

                // Run over the message attributes
                for &attr in &attrs[1..] {
                    val = match val {
                        Some(val) => match val {
                            Value::Object(map) => map.get(&attr),
                            other => Some(other), 
                        }
                        None => None,
                    }
                };

                match val {
                    Some(Value::Number(n)) => {
                        if n.is_f64() { return n.as_f64().unwrap().to_le_bytes().to_vec(); }
                        if n.is_i64() { return n.as_i64().unwrap().to_le_bytes().to_vec(); }
                        if n.is_u64() { return n.as_u64().unwrap().to_le_bytes().to_vec(); }
                        else { unreachable!("Expecting either i64, u64 or f64") }
                    },
                    Some(Value::String(s)) => unsafe { return s.as_mut_vec().to_vec(); },

                    None => unreachable!("Value should never be None!"), 
                    other => unreachable!("Value should be primitive (int, uint, float, string), got {:?}", other),
                };
            }
            Identifier::Variable(var) => unreachable!("Why would variables be needed ???"),
        };
    }
}