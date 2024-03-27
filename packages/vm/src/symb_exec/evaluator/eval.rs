use serde_json::{Value};

use crate::symb_exec::parser::nodes::{ArgTypes, Expr, Identifier, InputType, Integer, Number};

use super::super::parser::nodes::Key;

/// Serves as reference context for attribute accessors in SE-output.
/// 
/// Whenever there is an indentifier - ```var1``` or ```var1.field1```, we look
/// into all fields of SEContext to find a match, and get the corresponding
/// primitive type
pub struct SEContext<'a> {
    pub custom_msg: Value,
    pub arg_types: &'a ArgTypes,
    // TODO - need a way to also store the cosmwasm input types for each entry point
}

impl<'a> SEContext<'a> {
    pub fn default(arg_types: &'a ArgTypes) -> Self {
        SEContext { custom_msg: Value::Null, arg_types}
    }

    pub fn new(custom_msg: &[u8], arg_types: &'a ArgTypes) -> Self {
        let val: Value = serde_json::from_slice(custom_msg).expect("Failed to deserialize execute message");
        SEContext { custom_msg: val , arg_types }
    }

    pub fn get_var_type(&self, var_name: &String) -> Option<&InputType> {
        self.arg_types.get(var_name)
    }
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
    fn eval<F: Fn(&Vec<u8>) -> Vec<u8> + Clone>(&self, app_closure: &F, variable_context: &SEContext) -> Self::Output;
    fn op(lhs: &Self::Operand, op: &Self::Operator, rhs: &Self::Operand) -> Self::OpOut;
    
    /// Parses a Key into bytes.
    /// 
    /// Uses the ```app_closure``` to get the actual value bytes given the key bytes.
    /// Currently converts all data to Int type - TODO
    fn eval_storage_read<F>(&self, key: &Key, app_closure: &F, variable_context: &SEContext) -> Expr 
    where F: Fn(&Vec<u8>) -> Vec<u8> + Clone
    {
        let mut bytes;
        match key {
            Key::Bytes(key) => bytes = app_closure(key),
            Key::Expression { base, expr } => {
                bytes = base.clone();
                match expr.eval(app_closure, variable_context) {
                    Expr::Number(val) => match val {
                        Number::Float(f) => bytes.append(&mut f.to_le_bytes().to_vec()),
                        Number::Int(i)   => bytes.append(&mut i.to_le_bytes().to_vec())
                    },
                    Expr::Identifier(id) => bytes.append(&mut self.parse_identifier(&id, variable_context)),

                    // TODO - currently assuming a key can only be either a number or an identifier
                    r => unreachable!("Expected Number, or identifier, got {:?}", r), 
                };
            }
        };
        Expr::Number(Number::Int(Integer::from_be_bytes((*bytes).try_into().unwrap())))
    }

    /// Converts an identifier to the respective primitive type.
    /// This convertion is based on the received custom message, as well as on the
    /// Cosmwasm context types
    /// TODO - should return Expr & not bytes -> could be string, int, etc
    /// TODO - we are currently only checking attr accessors in the custom msg
    fn parse_identifier(&self, id: &Identifier, variable_context: &SEContext) -> Vec<u8> {
        match id {
            // fetch 1st identifier in the access sequence & check which type it is from the inputs
            Identifier::AttrAccessor(attrs) => {
                let variable = attrs.get(0).unwrap();
                match variable_context.get_var_type(variable) {
                    Some(InputType::DepsMut)     => vec![0x00],
                    Some(InputType::Env)         => vec![0x00],
                    Some(InputType::MessageInfo) => vec![0x00],
                    Some(InputType::Custom)      => {
                        let expr = self.parse_custom_msg_identifier(&attrs[1..], variable_context);
                        match expr.as_bytes() {
                            Some(bytes) => bytes,
                            None => unreachable!("Expected bytes from primitive expression type. Expression used is not primitive (number/string)")
                        }
                    },
                    None => unreachable!("Variables should always reference one of the inputs...")
                }
            }
            Identifier::Variable(_) => unreachable!("Why would variables be needed ???"),
        }
    }

    fn parse_custom_msg_identifier(&self, attrs: &[String], variable_context: &SEContext) -> Expr {
        // get the actual object with contents (get rid of message type)
        let mut val = Some(match &variable_context.custom_msg {
            Value::Object(v) => {
                if let Some((_, val)) = v.into_iter().next() {
                    val
                } else { unreachable!("Custom msg should always have at least 1 object") }
            },
            v => unreachable!("Expecting json object, got {:?}", v)
        });

        // Run over the message attributes & try to find a match
        for attr in attrs {
            val = match val {
                // whil val is a json Value::Object, keep going
                Some(val) => match val {
                    Value::Object(map) => map.get(attr),
                    other => Some(other), 
                }
                None => unreachable!("Could not match attribute accessor to custom msg"),
            };
        };

        // return the corresponding primitive type
        match val {
            Some(Value::Number(n)) => {
                if n.is_f64() { return Expr::Number(Number::Float(n.as_f64().unwrap())); }
                if n.is_i64() { return Expr::Number(Number::Int(n.as_i64().unwrap())); }
                if n.is_u64() { return Expr::Number(Number::Int(n.as_i64().unwrap())); }
                else { unreachable!("Expecting either i64, u64 or f64") }
            },
            Some(Value::String(s)) => return Expr::String(s.clone()),

            None => unreachable!("Value should never be None!"), 
            other => unreachable!("Value should be primitive (int, uint, float, string), got {:?}", other),
        };
    }
}

#[cfg(test)]
mod tests {
    use crate::symb_exec::parser::nodes::ArgTypes;

    use super::{Eval, SEContext};


    struct DefaultImpl {}
    impl Eval for DefaultImpl {
        type Output = i32;
        type Operand = i32;
        type Operator = i32;
        type OpOut = i32;
    
        fn eval<F: Fn(&Vec<u8>) -> Vec<u8> + Clone>(&self, _: &F, _: &super::SEContext) -> Self::Output {
            todo!()
        }
    
        fn op(_: &Self::Operand, _: &Self::Operator, _: &Self::Operand) -> Self::OpOut {
            todo!()
        }
    }

    fn default_context(arg_types: &ArgTypes) -> SEContext {
        SEContext::new(br#"
            {
                "Adduser": {
                    "admin": "name1",
                    "balance": 2,
                    "fee": 2.543,
                    "neg": -5,
                    "InternalObj": {
                        "field1": "still works",
                    }
                }
            }"#, 
            arg_types
        )
    }

    #[test]
    fn parse_custom_msg_identifier() {
        let def = DefaultImpl {};


    }
}