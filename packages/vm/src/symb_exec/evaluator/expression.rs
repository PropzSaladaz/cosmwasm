use super::super::parser::nodes::*;
use super::eval::{Eval, SEContext, StorageAccessor};

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Expr::Number(a), Expr::Number(b)) => {
                a == b
            }, 
            (Expr::String(a), Expr::String(b)) => {
                a == b
            }
            content => unreachable!("Expected primitive types only, got {:?}", content),
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
            }
            content => unreachable!("Expected primitive types only, got {:?}", content),
        }
    }
}

impl Eval for Expr {
    type Output = Expr;
    type Operand = Number;
    type Operator = Op;
    type OpOut = Number;

    /// Evaluate an expression at runtime - Evalautes storage reads through the input app_closure
    /// Anything evaluated through an expression returns a number or a string
    fn eval<F: StorageAccessor>(&self, app_closure: &F, variable_context: &SEContext) -> Self::Output 
    {
        match self {
            Self::BinOp { 
                lhs, 
                op, 
                rhs 
            } => match (&**lhs, &**rhs) { (a, b) => 
                {
                    let num_a = match a.eval(app_closure, variable_context) {
                        Expr::Number(num) => num,
                        nan => unreachable!("Expected a number, found {:?}", nan),
                    };
                    let num_b = match b.eval(app_closure, variable_context) {
                        Expr::Number(num) => num,
                        nan => unreachable!("Expected a number, found {:?}", nan),
                    };
                    Expr::Number(Self::op(&num_a, op, &num_b))
                }                
            },

            Self::Identifier(id) => {
                let tmp = self.parse_identifier(id, variable_context);
                match tmp {
                    Expr::Number(n) => Expr::Number(n),
                    Expr::String(s) => Expr::String(s),
                    other => unreachable!("Expecting only primitive (number/string) types as Expr::Identifier, got {:?}", other)
                }
            },

            Self::StorageRead(key) => self.eval_storage_read(key, app_closure, variable_context),

            Self::MessageType(id) => Expr::MessageType(id.clone()),
            Self::Type(ty) => Expr::Type(ty.clone()),
            Self::String(s) => Expr::String(s.clone()),
            Self::Number(numb) => Expr::Number(numb.clone()),
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
            Expr::Number(Number::Float(4.5))
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
            Expr::Number(Number::Float(16.5))
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
            Expr::Number(Number::Float(31.5))
        );
    }
}