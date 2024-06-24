use cosmwasm_std::Storage;
use serde_json::{Value};

use crate::symb_exec::{parser::nodes::{ArgTypes, CosmwasmInputs, Expr, Identifier, InputType, Integer, Number, Type}, ReadWrite};

use super::super::parser::nodes::Key;

/// Serves as reference context for attribute accessors in SE-output.
/// 
/// Whenever there is an indentifier - ```var1``` or ```var1.field1```, we look
/// into all fields of SEContext to find a match, and get the corresponding
/// primitive type.
pub struct SEContext<'a, 'b> {
    // stores the full custom msg, the input variable names
    pub custom_msg: Value,
    
    // mapping between input identifier - input type
    pub arg_types: &'a ArgTypes,

    // stores the actual dynamic inputs of the entry call, passed by the VM
    pub cosmwasm_types: CosmwasmInputs<'b>
}

impl<'a, 'b> SEContext<'a, 'b> {
    pub fn default(arg_types: &'a ArgTypes) -> Self {
        SEContext { custom_msg: Value::Null, arg_types, cosmwasm_types: CosmwasmInputs::Mock}
    }

    pub fn new(custom_msg: &[u8], arg_types: &'a ArgTypes, cosmwasm_types: CosmwasmInputs<'b>) -> Self {
        let val: Value = serde_json::from_slice(custom_msg).expect("Failed to deserialize execute message");
        SEContext { custom_msg: val , arg_types , cosmwasm_types }
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
    fn eval(&self, storage: &dyn Storage, variable_context: &SEContext) -> Self::Output;

    /// Applies a binary operation given the specified Operand types, as well 
    /// as the Operator and Output type
    fn op(lhs: &Self::Operand, op: &Self::Operator, rhs: &Self::Operand) -> Self::OpOut;
    
    /// Parses a Key into bytes and uses the ```storage``` to get the actual value bytes given the key bytes.
    /// 
    /// Currently converts all data to Int type - TODO
    fn eval_storage_read(&self, key: &Key, storage: &dyn Storage, variable_context: &SEContext) -> Expr 
    {
        let bytes;
        match key {
            Key::Bytes(key) => bytes = storage.get(key),
            Key::Expression { base, expr } => {
                let mut bytes_tmp = base.clone();
                let expr = expr.eval(storage, variable_context);
                let mut option_bytes = expr.as_bytes();
                match &mut option_bytes {
                    Some(bytes) => bytes_tmp.append(bytes),
                    None => unreachable!("Could not convert expression to bytes"),
                } 
                bytes = storage.get(&bytes_tmp);
            }
        };

        // TODO - currently converting all data to Int - This was used when we had expressions.
        // Now we only need to mark the reads/writes as commutative/non-commutative
        match bytes {
            Some(bytes) => Expr::Number(Number::Int(Integer::from_le_bytes(
                [bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6] , bytes[7]]))),
            None => Expr::Null,
        }
        
    }

    /// Converts an identifier to the respective primitive type.
    /// This convertion is based on the received custom message, as well as on the
    /// Cosmwasm context types.
    /// 
    /// TODO - we are currently only checking attr accessors in the custom msg
    fn parse_identifier(&self, id: &Identifier, variable_context: &SEContext) -> Expr {
        match id {
            // fetch 1st identifier in the access sequence & check which type it is from the inputs
            Identifier::AttrAccessor(attrs) => {
                let variable = attrs.get(0).unwrap();
                match variable_context.get_var_type(variable) {
                    Some(InputType::DepsMut)     => todo!(),
                    Some(InputType::Env)         => todo!(),
                    Some(InputType::MessageInfo) => todo!(),
                    Some(InputType::Custom)      => self.parse_custom_msg_identifier(&attrs[1..], variable_context),
                    None => unreachable!("Variables should always reference one of the inputs...")
                }
            }

            // TODO - Currently, if we have an identifier that isn't an attribute accessor, we assume
            // it will be used to identify some type. This is used in expressions like: Type(_msg) == DepsMut
            // where we use this Identifier branch to describe the "DepsMut" type
            Identifier::Variable(_) => {
                // TODO - we should look first in context to try match the variable &
                // only then return a string
                Expr::Identifier(id.clone())
            },
        }
    }

    /// Parses a variable/attribute accessor referencing to some field in the custom
    /// json message given as input to the Smart Contract.
    /// 
    /// Evaluates from a slice of strings to the corresponding primitive value.
    /// 
    /// TODO - Currently only supporting Number & String
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

            None => unreachable!("Attribute does not exist in custom message"), 
            other => unreachable!("Value should be primitive (int, float, string), got {:?}", other),
        };
    }


    /// Fetch the type given a identifier.
    /// It is either an input variable, which can include the 
    /// cosmwas contract input types (DepsMut, etc), and also the custom type.
    /// 
    /// If it refers to the custom input type, then the type refers to the enum variant
    /// of the message and not the message itself.
    /// 
    /// It can also be a primitive type inside an attr accessor such as `msg.field1`
    fn parse_type(&self, id: &Identifier, variable_context: &SEContext) -> Expr {
        match id {
            Identifier::Variable(v) => {
                match variable_context.get_var_type(v) {
                    Some(InputType::DepsMut)     => Expr::Type(Type::Custom("DepsMut".to_owned())),
                    Some(InputType::Env)         => Expr::Type(Type::Custom("Env".to_owned())),
                    Some(InputType::MessageInfo) => Expr::Type(Type::Custom("MessageInfo".to_owned())),
                    Some(InputType::Custom)      =>  {
                        match &variable_context.custom_msg {
                            Value::Object(v) => {
                                if let Some((key, _)) = v.into_iter().next() {
                                    Expr::Type(Type::Custom(key.to_owned()))
                                } else { unreachable!("Custom msg should always have at least 1 object") }
                            },
                            v => unreachable!("Expecting json object, got {:?}", v)
                        }
                    }
                    None => unreachable!("Variables should always reference one of the inputs...")
                }
            },
            Identifier::AttrAccessor(_) => {
                match self.parse_identifier(id, variable_context) {
                    Expr::Number(n) => match n {
                        Number::Float(_) => Expr::Type(Type::Float),
                        Number::Int(_) => Expr::Type(Type::Int),
                    },
                    Expr::String(_) => Expr::Type(Type::String),
                    other => unreachable!("Attr accessors should have primitive types, got {:?}", other)
                }
            }
        }
    }
}


impl ReadWrite {
    /// Used to evaluate final RWS keys into actual values.
    /// RWS is first built into a well-structured tree, like so:
    /// 
    /// Expr::StorageRead(Key::Expression { 
    /// 
    ///  base: key_raw.to_vec(), 
    /// 
    ///  expr: Box::new(Expr::Identifier(Identifier::AttrAccessor(vec![
    /// 
    ///   "msg".to_owned(), 
    /// 
    ///   "admin".to_owned()])))
    /// 
    ///  }
    /// 
    /// )
    /// 
    /// This evaluation turns key expressions into values. In the above example, turns `msg.admin` into `"name1"` by
    /// fetching the value of `msg.admin` from the current variable_context.
    /// 
    /// In the general case, it turns Get(base @ expr) into Get(bytes), by evaluating `expr`
    /// and appending it to the base. This way we have concrete keys.
    pub fn eval(&mut self, storage: &dyn Storage, variable_context: &SEContext) -> Self {   
        match self {
            Self::Read {
                storage_dependency,
                key,
                commutativity
            } => Self::Read {
                storage_dependency: *storage_dependency,
                key: key.eval(storage, variable_context),
                commutativity: *commutativity
            },
            Self::Write { 
                storage_dependency,
                key, 
                commutativity 
            } => Self::Write {
                storage_dependency: *storage_dependency, 
                key: key.eval(storage, variable_context), 
                commutativity: *commutativity
            }
        }
    }
}

impl Key {
    pub fn eval(&mut self, storage: &dyn Storage, variable_context: &SEContext) -> Self {
        match self {
            Key::Bytes(b) => Key::Bytes(b.clone()),
            Key::Expression { base, expr } => {
                let mut bytes_tmp = base.clone();
                let expr = expr.eval(storage, variable_context);
                let mut option_bytes = expr.as_bytes();
                match &mut option_bytes {
                    Some(bytes) => bytes_tmp.append(bytes),
                    None => unreachable!("Could not convert expression to bytes"),
                };
                Key::Bytes(bytes_tmp)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::symb_exec::testing::mock::*;

    use super::super::super::parser::{nodes::*, nodes::TransactionDependency::*};

    use super::*;


    /// Simulates some concrete implementor - used to test default Eval methods
    struct DefaultImpl {}
    impl Eval for DefaultImpl {
        type Output = i32;
        type Operand = i32;
        type Operator = i32;
        type OpOut = i32;
    
        fn eval(&self, _: &dyn Storage, _: &super::SEContext) -> Self::Output {
            todo!()
        }
    
        fn op(_: &Self::Operand, _: &Self::Operator, _: &Self::Operand) -> Self::OpOut {
            todo!()
        }
    }

    #[test]
    fn eval_parse_custom_msg_identifier() {
        let imp = DefaultImpl {};
        let arg_types = ArgTypes::new();
        let ctx = mock_context(&arg_types);

        let expr = imp.parse_custom_msg_identifier(
            &["InternalObj".to_owned(), "field1".to_owned()], 
            &ctx);
        
        assert_eq!(expr, Expr::String(String::from("still works")));

        let expr = imp.parse_custom_msg_identifier(
            &["admin".to_owned()], 
            &ctx);
        
        assert_eq!(expr, Expr::String(String::from("name1")));

        let expr = imp.parse_custom_msg_identifier(
            &["balance".to_owned()], 
            &ctx);
        
        assert_eq!(expr, Expr::Number(Number::Int(2)));

        let expr = imp.parse_custom_msg_identifier(
            &["fee".to_owned()], 
            &ctx);
        
        assert_eq!(expr, Expr::Number(Number::Float(2.543)));


        let expr = imp.parse_custom_msg_identifier(
            &["neg".to_owned()], 
            &ctx);
        
        assert_eq!(expr, Expr::Number(Number::Int(-5)));
    }

    #[test]
    fn eval_parse_identifier() {
        let imp = DefaultImpl {};
        let arg_types = mock_arg_types();
        let ctx = mock_context(&arg_types);

        let expr = imp.parse_identifier(
            // msg.balance - from mock_arg_types, we defined "msg" as the variable name
            // for the user custom message, thus we look into the attribute "balance" of
            // user custom message.
            &Identifier::AttrAccessor(vec!["msg".to_owned(), "balance".to_owned()]),
            &ctx);
        
        assert_eq!(expr, Expr::Number(Number::Int(2)));

        // TODO - test the other cases -> when searching for the input var in 
        // the other input args instead of user's json message only 
    }

    #[test]
    fn eval_storage_read_base_bytes() {
        let imp = DefaultImpl {};
        let arg_types = mock_arg_types();
        let ctx = mock_context(&arg_types);

        let key_raw = vec![1u8];
        let key_val_raw = vec![10u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
        let storage = mock_storage(HashMap::from([(key_raw.clone(), key_val_raw)]));

        let key = Key::Bytes(key_raw.to_vec());

        let expr = imp.eval_storage_read(&key, &storage, &ctx);

        assert_eq!(
            expr,
            // TODO - Currently explicitly converting storage reads to Int
            Expr::Number(Number::Int(Integer::from_le_bytes([10u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])))
        )
    }

    #[test]
    fn eval_storage_read_expression() {
        let imp = DefaultImpl {};
        let arg_types = mock_arg_types();
        let ctx = mock_context(&arg_types);

        let key_raw = vec![1u8];
        let key_val_raw = vec![10u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
        let expr_bytes = "name1".as_bytes();
        // Get(base @ "msg.admin")
        let mut expected_key = key_raw.clone();
        expected_key.append(&mut expr_bytes.to_vec());
        
        let storage = mock_storage(HashMap::from([(expected_key, key_val_raw)]));

        let key = Key::Expression { 
            base: key_raw.to_vec(), 
            expr: Box::new(Expr::Identifier(Identifier::AttrAccessor(vec![
                "msg".to_owned(), 
                "admin".to_owned()
            ])))
        };

        let expr = imp.eval_storage_read(&key, &storage, &ctx);

        assert_eq!(
            expr,
            // TODO - Currently explicitly converting storage reads to Int
            Expr::Number(Number::Int(Integer::from_le_bytes([10u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8])))
        )
    }

    #[test]
    fn eval_parse_type() {
        let imp = DefaultImpl {};
        let arg_types = mock_arg_types();
        let ctx = mock_context(&arg_types);

        let id = Identifier::Variable("msg".to_owned());
        let expr = imp.parse_type(&id, &ctx);

        assert_eq!(expr, Expr::Type(Type::Custom("AddUser".to_owned())));

        let id = Identifier::Variable("deps".to_owned());
        let expr = imp.parse_type(&id, &ctx);

        assert_eq!(expr, Expr::Type(Type::Custom("DepsMut".to_owned())));

        let id = Identifier::Variable("env".to_owned());
        let expr = imp.parse_type(&id, &ctx);

        assert_eq!(expr, Expr::Type(Type::Custom("Env".to_owned())));

        let id = Identifier::Variable("info".to_owned());
        let expr = imp.parse_type(&id, &ctx);

        assert_eq!(expr, Expr::Type(Type::Custom("MessageInfo".to_owned())));

        let id = Identifier::AttrAccessor(vec![
            "msg".to_owned(), "admin".to_owned()]);
        let expr = imp.parse_type(&id, &ctx);

        assert_eq!(expr, Expr::Type(Type::String));

        let id = Identifier::AttrAccessor(vec![
            "msg".to_owned(), "balance".to_owned()]);
        let expr = imp.parse_type(&id, &ctx);

        assert_eq!(expr, Expr::Type(Type::Int));

        let id = Identifier::AttrAccessor(vec![
            "msg".to_owned(), "fee".to_owned()]);
        let expr = imp.parse_type(&id, &ctx);

        assert_eq!(expr, Expr::Type(Type::Float));
    }

    #[test]
    fn eval_rws() {
        let arg_types = mock_arg_types();
        let ctx = mock_context(&arg_types);

        let key_raw = vec![1u8];
        // number 1 in big-endian
        let key_val_raw = vec![1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
        let expr_bytes = "name1".as_bytes();
        // Get(base @ "msg.admin")
        let mut expected_key = key_raw.clone();
        expected_key.append(&mut expr_bytes.to_vec());
        
        let storage = mock_storage(HashMap::from([(expected_key.clone(), key_val_raw)]));

        let mut rws = vec![
            // Get(1u8 @ msg.admin)
            ReadWrite::Read{
                storage_dependency: INDEPENDENT,
                key: Key::Expression { 
                    base: key_raw.to_vec(), 
                    expr: Box::new(Expr::Identifier(Identifier::AttrAccessor(vec![
                        "msg".to_owned(), 
                        "admin".to_owned()
                    ])))
                },
                commutativity: WriteType::Commutative,
            },
            // Set(1u8 @ msg.admin): Inc
            ReadWrite::Write { 
                storage_dependency: INDEPENDENT,
                key: Key::Expression { 
                    base: key_raw.to_vec(), 
                    expr: Box::new(Expr::Identifier(Identifier::AttrAccessor(vec![
                        "msg".to_owned(), 
                        "admin".to_owned()
                    ]))) 
                }, 
                commutativity: WriteType::Commutative 
            }  
        ];

        let expr: Vec<_> = rws.iter_mut().map(|rws| 
            rws.eval(&storage, &ctx)).collect();

        assert_eq!(
            expr,
            vec![
                ReadWrite::Read {
                    storage_dependency: INDEPENDENT,
                    key: Key::Bytes(expected_key.clone()),
                    commutativity: WriteType::Commutative,
                },
                ReadWrite::Write { 
                    storage_dependency: INDEPENDENT,
                    key: Key::Bytes(expected_key), 
                    commutativity: WriteType::Commutative
                }
            ]
        )
    }
}