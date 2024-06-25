use cosmwasm_std::Storage;

use super::super::parser::nodes::*;
use super::eval::{Eval, SEContext};

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Expr::Null, Expr::Null)          => true,
            (Expr::Null, _) | (_, Expr::Null) => false,

            // default same-type comparisons
            (Expr::Number(a),         Expr::Number(b))          => a == b, 
            (Expr::String(a),         Expr::String(b))          => a == b,
            (Expr::MessageType(a),    Expr::MessageType(b))     => a == b,
            (Expr::Identifier(a), Expr::Identifier(b))  => a == b,
            (Expr::StorageRead(a),       Expr::StorageRead(b))        => a == b,

            // Type checking between 2 types - "Type(a) == Type(b)"
            (Expr::Type(a),             Expr::Type(b))              => a == b,
            
            // Type checking for custom messages - "Type(msg) == SomeType"
            (Expr::Type(Type::Custom(a)), Expr::MessageType(b)) => a == b,
            
            // Type checking for custom types - "Type(msg) == SomeType"
            (Expr::Type(Type::Custom(a)), Expr::Identifier(Identifier::Variable(b))) |
            (Expr::Identifier(Identifier::Variable(b)), Expr::Type(Type::Custom(a))) => a == b,


            (Expr::BinOp { lhs: lhs1, op: op1, rhs: rhs1 }, 
             Expr::BinOp { lhs: lhs2, op: op2, rhs: rhs2 }) => 
                lhs1 == lhs2 && op1 == op2 && rhs1 == rhs2,
            
            // We do not consider the dependency for the equality, as this equality is strictly for the expression
            (Expr::Result { expr: e_a, dependency: _ }, 
             Expr::Result { expr: e_b, dependency: _ }) => e_a == e_b,

            o => unreachable!("cannot compare {:?}", o)
        }
    }
}

impl PartialOrd for Expr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Expr::Number(a), Expr::Number(b)) => {
                a.partial_cmp(b)
            },
            (Expr::String(a), Expr::String(b)) => {
                a.partial_cmp(b)
            },
            (Expr::Result { expr: e_a, dependency: _ }, Expr::Result { expr: e_b, dependency: _ }) => {
                e_a.partial_cmp(e_b)
            },
            content => unreachable!("Expected comparison between 2 primitive types of same type, got {:?}", content),
        }
    }
}

impl Eval for Expr {
    type Output = Expr;
    type Operand = Number;
    type Operator = Op;
    type OpOut = Number;

    /// Evaluate an expression at runtime - Evalautes storage reads through the input storage
    /// Anything evaluated through an expression returns a number or a string
    fn eval(&self, storage: &dyn Storage, variable_context: &SEContext) -> Self::Output 
    {
        match self {
            Self::BinOp { 
                lhs, 
                op, 
                rhs 
            } => match (&**lhs, &**rhs) { 
                (l, r) => {
                    let num_a = match l.eval(storage, variable_context) {
                        Expr::Result { expr, dependency }  => match *expr {
                            Expr::Number(num) => (num, dependency),
                            other => unreachable!("Expected a number, got {:?}", other),
                        },
                        other => unreachable!("Expected a Expr::Result, found {:?}", other),
                    };

                    let num_b = match r.eval(storage, variable_context) {
                        Expr::Result { expr, dependency }  => match *expr {
                            Expr::Number(num) => (num, dependency),
                            other => unreachable!("Expected a number, got {:?}", other),
                        },
                        other => unreachable!("Expected a Expr::Result, found {:?}", other),
                    };

                    let dependency = num_a.1 | num_b.1;

                    Expr::Result { expr: Box::new(Expr::Number(Self::op(&num_a.0, op, &num_b.0))), dependency }
                },           
            },

            Self::Identifier(id) => {
                let tmp = self.parse_identifier(id, variable_context);
                match tmp {
                    Expr::Number(n)          => Self::Result { expr: Box::new(Expr::Number(n)),      dependency: StorageDependency::Independent },
                    Expr::String(s)          => Self::Result { expr: Box::new(Expr::String(s)),      dependency: StorageDependency::Independent },
                    Expr::Identifier(id) => Self::Result { expr: Box::new(Expr::Identifier(id)), dependency: StorageDependency::Independent },
                    other => unreachable!("Expecting only primitive (number/string/Identifier) types as Expr::Identifier, got {:?}", other)
                }
            },

            Self::Type(ty) => {
                match ty {
                    Type::Expr(e) => match &**e {
                        Expr::Number(n) => match n {
                            Number::Float(_) => Self::Result { expr: Box::new(Expr::Type(Type::Float)), dependency: StorageDependency::Independent },
                            Number::Int(_)   => Self::Result { expr: Box::new(Expr::Type(Type::Int)),   dependency: StorageDependency::Independent },
                        },
                        Expr::String(_)                  => Self::Result { expr: Box::new(Expr::Type(Type::String)),                 dependency: StorageDependency::Independent },
                        Expr::Identifier(i) => Self::Result { expr: Box::new(self.parse_type(&i, variable_context)), dependency: StorageDependency::Independent },
                        other                     => Self::Result { expr: Box::new(Expr::Type(Type::Expr(Box::new(other.eval(storage, variable_context))))), 
                            dependency: StorageDependency::Independent },
                    },
                    leaf_type => Self::Result { expr: Box::new(Expr::Type(leaf_type.clone())), dependency: StorageDependency::Independent },
                }
            },

            // Primitive types - Below are the root types after which the evaluation's recursiveness ends, and we start returning the results of evaluation
            Self::StorageRead(key)   => Self::Result { expr: Box::new(self.eval_storage_read(key, storage, variable_context)), dependency: StorageDependency::Dependent },
            // we should check if is either a variable vs. attribute accessor
            Self::MessageType(id) => Self::Result { expr: Box::new(Expr::MessageType(id.clone())),                          dependency: StorageDependency::Independent },

            Self::String(s)       => Self::Result { expr: Box::new(Expr::String(s.clone())),                                dependency: StorageDependency::Independent },

            Self::Number(numb)    => Self::Result { expr: Box::new(Expr::Number(numb.clone())),                             dependency: StorageDependency::Independent },
            
            Self::Null                     => Self::Result { expr: Box::new(Expr::Null),                                             dependency: StorageDependency::Independent },

            Self::Result { expr: _, dependency: _ } => self.clone(),
        }
    }

    fn op(lhs: &Self::Operand, op: &Self::Operator, rhs: &Self::Operand) -> Self::OpOut {
        match &op {
            Op::Add      => *lhs + *rhs,
            Op::Subtract => *lhs - *rhs,
            Op::Multiply => *lhs * *rhs,
            Op::Divide   => *lhs / *rhs,
            _ => unreachable!("Pow not supported yet")
        }
    }

}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::symb_exec::testing::mock::{mock_arg_types, mock_context, mock_storage};

    use super::*;

    #[test]
    fn expr_cmp_number() {
        // Equality
        assert_eq!(
            Expr::Number(Number::Float(4.5)), 
            Expr::Number(Number::Float(4.5))
        );
        assert_ne!(
            Expr::Number(Number::Float(1.5)), 
            Expr::Number(Number::Float(4.5))
        );
        assert_eq!(
            Expr::Number(Number::Int(4)), 
            Expr::Number(Number::Int(4))
        );
        assert_ne!(
            Expr::Number(Number::Int(2)), 
            Expr::Number(Number::Int(4))
        );

        // Inequality
        assert!(Expr::Number(Number::Int(5)) > Expr::Number(Number::Int(4)));
        assert!(Expr::Number(Number::Int(1)) < Expr::Number(Number::Int(4)));
        assert!(Expr::Number(Number::Float(5.0)) >= Expr::Number(Number::Float(5.0)));
        assert!(Expr::Number(Number::Float(5.55)) > Expr::Number(Number::Float(4.2)));
    }

    #[test]
    fn expr_cmp_string() {
        assert_eq!(
            Expr::String(String::from("hello")), 
            Expr::String(String::from("hello"))
        );
        assert_ne!(
            Expr::String(String::from("hello")), 
            Expr::String(String::from("world"))
        );

        assert!(Expr::String(String::from("hello")) > Expr::String(String::from("h")));
    }

    #[test]
    fn expr_cmp_type() {
        assert_eq!(
            Expr::Type(Type::Custom("AddUser".to_owned())),
            Expr::Identifier(Identifier::Variable("AddUser".to_owned()))
        );
        assert_eq!(
            Expr::Identifier(Identifier::Variable("AddUser".to_owned())),
            Expr::Type(Type::Custom("AddUser".to_owned()))
        );

        assert_ne!(
            Expr::Identifier(Identifier::Variable("int".to_owned())),
            Expr::Type(Type::Custom("AddUser".to_owned()))
        );
    }


    #[test]
    fn expr_numbers() {
        // 1.5 + (1.5 * 2)
        let init = Expr::BinOp { 
            lhs: Box::new(Expr::Number(Number::Float(1.5))), 
            op: Op::Add, 
            rhs: Box::new(Expr::BinOp { 
                lhs: Box::new(Expr::Number(Number::Float(1.5))), 
                op: Op::Multiply, 
                rhs: Box::new(Expr::Number(Number::Int(2))), 
            }) 
        };

        let storage = mock_storage(HashMap::new());
        let arg_types = mock_arg_types();
        let context = mock_context(&arg_types);

        assert_eq!(
            init.eval( &storage, &context), 
            Expr::Result {
                expr: Box::new(Expr::Number(Number::Float(4.5))),
                dependency: StorageDependency::Independent,
            }
        );
    }

    #[test]
    fn expr_storage_read() {
        // 1.5 + (Get(0x00) * 3.0)
        let init = Expr::BinOp { 
            lhs: Box::new(Expr::Number(Number::Float(1.5))), 
            op: Op::Add, 
            rhs: Box::new(Expr::BinOp { 
                lhs: Box::new(
                    // the bytes are irrelevant - we are always returning 5 as the value stored
                    Expr::StorageRead(Key::Bytes(vec![0u8]))),  
                op: Op::Multiply, 
                rhs: Box::new(
                    Expr::Number(Number::Float(3.0))
                ), 
            }) 
        };


        let key_raw = vec![0u8];
        let val_raw = vec![5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]; // int 5 in little-endian
        let storage = mock_storage(HashMap::from([(key_raw, val_raw)]));
        let arg_types = mock_arg_types();
        let context = mock_context(&arg_types);

        assert_eq!(
            init.eval(&storage, &context), 
            Expr::Result {
                expr: Box::new(Expr::Number(Number::Float(16.5))),
                dependency: StorageDependency::Dependent,
            }
        );
    }

    #[test]
    fn expr_storage_read_recursive() {
        // 1.5 + (Get(0x00 @ (Get(0x00) - 2) ) * 3.0)
        let init = Expr::BinOp { 
            lhs: Box::new(Expr::Number(Number::Float(1.5))), 
            op: Op::Add, 
            rhs: Box::new(Expr::BinOp { 
                // This read should return 10
                lhs: Box::new(Expr::StorageRead(Key::Expression{
                        base: vec![0u8],
                        expr: Box::new(Expr::BinOp { 
                            // This read should return 5
                            lhs: Box::new(Expr::StorageRead(Key::Bytes(vec![0u8]))), 
                            op: Op::Subtract, 
                            rhs: Box::new(Expr::Number(Number::Int(2))) 
                        })
                    })),  
                op: Op::Multiply, 
                rhs: Box::new(
                    Expr::Number(Number::Float(3.0))
                ), 
            }) 
        };


        let key1_raw = vec![0u8];
        let val1_raw = vec![5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]; // int 5 in little-endian

        let mut key2_raw = vec![0u8];
        // we want the value at key 0x00 @ 5-2 = 0x00 @ 3
        key2_raw.append(&mut vec![3u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]); // append int 3 in little-endian
        let val2_raw = vec![10u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]; // int 10 in little-endian


        let storage = mock_storage(HashMap::from([
            (key1_raw, val1_raw),
            (key2_raw, val2_raw)
        ]));

        let arg_types = mock_arg_types();
        let context = mock_context(&arg_types);

        assert_eq!(
            init.eval(&storage, &context), 
            Expr::Result {
                expr: Box::new(Expr::Number(Number::Float(31.5))),
                dependency: StorageDependency::Dependent,
            }
        );
    }

    #[test]
    fn expr_type() {
        let arg_types = mock_arg_types();
        let ctx = mock_context(&arg_types);
        let storage = mock_storage(HashMap::new());

        let expr = Expr::Type(
            Type::Expr(Box::new(
                Expr::Identifier(Identifier::AttrAccessor(
                vec!["msg".to_owned(), "admin".to_owned()])))));
        let expr = expr.eval(&storage, &ctx);

        assert_eq!(expr, Expr::Result { expr: Box::new(Expr::Type(Type::String)), dependency: StorageDependency::Independent });

        let expr = Expr::Type(
            Type::Expr(Box::new(
                Expr::Identifier(Identifier::AttrAccessor(
                vec!["msg".to_owned(), "balance".to_owned()])))));
        let expr = expr.eval(&storage, &ctx);

        assert_eq!(expr, Expr::Result { expr: Box::new(Expr::Type(Type::Int)), dependency: StorageDependency::Independent });

        let expr = Expr::Type(
            Type::Expr(Box::new(
                Expr::Identifier(Identifier::AttrAccessor(
                vec!["msg".to_owned(), "fee".to_owned()])))));
        let expr = expr.eval(&storage, &ctx);

        assert_eq!(expr, Expr::Result { expr: Box::new(Expr::Type(Type::Float)), dependency: StorageDependency::Independent });
    }
}