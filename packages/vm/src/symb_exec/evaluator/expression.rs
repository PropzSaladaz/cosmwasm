use bytes::BufMut;
use num::traits::ToBytes;
use serde_json::Value;

use super::super::parser::nodes::*;
use super::eval::{Eval, SEContext};

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Expr::Number(a), Expr::Number(b)) => {
                a == b
            }, // TODO implement also comparison for strings!
            content => unreachable!("Expected numbers only, got {:?}", content),
        }
    }
}

impl PartialOrd for Expr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Expr::Number(a), Expr::Number(b)) => {
                a.partial_cmp(b)
            }, // TODO implement also comparison for strings!
            content => unreachable!("Expected numbers only, got {:?}", content),
        }
    }
}

impl Eval for Expr {
    type Output = Expr;
    type Operand = Number;
    type Operator = Op;
    type OpOut = Number;

    /// Evaluate an expression at runtime - Evalautes storage reads through the input app_closure
    /// Anything evaluated through an expression returns a number - either Integer or Float
    fn eval<F>(self, app_closure: &F, variable_context: &SEContext) -> Self::Output 
    where F: Fn(Vec<u8>) -> Vec<u8> + Clone
    {
        match self {
            Self::BinOp { 
                lhs, 
                op, 
                rhs 
            } => match (*lhs, *rhs) { 
                // TODO - When we do this parsing for both lhs and rhs, we should be calling the .eval on those expressions..
                // we should not be converting storage reads here ourselves. this is done below
                ( Expr::Number(a), Expr::Number(b)) 
                => Expr::Number(Self::op(a, op, b)),

                ( Expr::Number(a), Expr::StorageRead(key) ) 
                => {
                    // TODO EXPLICIT CONVERSION TO INT!!!!! - Assuming everything is int
                    if let Expr::Number(val) = self.eval_storage_read(key, &app_closure, &variable_context) {
                        Expr::Number(Self::op(a, op, val))
                    } else { unreachable!("Currently only parsing reads as Ints") }
                }

                ( Expr::StorageRead(key), Expr::Number(a) ) 
                => {
                    // TODO EXPLICIT CONVERSION TO INT!!!!! - Assuming everything is int
                    if let Expr::Number(val) = self.eval_storage_read(key, &app_closure, &variable_context) {
                        Expr::Number(Self::op(val, op, a))
                    } else { unreachable!("Currently only parsing reads as Ints") }
                }

                ( Expr::StorageRead(key_a), Expr::StorageRead(key_b) ) 
                => {
                    // TODO EXPLICIT CONVERSION TO INT!!!!! - Assuming everything is int
                    if let Expr::Number(val_a) = self.eval_storage_read(key_a, &app_closure, &variable_context) {
                        if let Expr::Number(val_b) = self.eval_storage_read(key_b, &app_closure, &variable_context) {
                            Expr::Number(Self::op(val_a, op, val_b))
                        } else { unreachable!("Currently only parsing reads as Ints") }
                    } else { unreachable!("Currently only parsing reads as Ints") }

                }
                
                (a, b) => {
                    let num_a = match a.eval(&app_closure, &variable_context) {
                        Expr::Number(num) => num,
                        nan => unreachable!("Expected a number, found {:?}", nan),
                    };
                    let num_b = match b.eval(&app_closure, &variable_context) {
                        Expr::Number(num) => num,
                        nan => unreachable!("Expected a number, found {:?}", nan),
                    };
                    Expr::Number(Self::op(num_a, op, num_b))
                }                
            },
            // TODO Identifiers not supported Yet! - should use the app_closure
            Self::Identifier(id) => self.parse_identifier(id, &variable_context),
            Self::MessageType(id) => Expr::MessageType(id),
            Self::Type(ty) => Expr::Type(ty),
            Self::String(s) => Expr::String(s),

            Self::StorageRead(key) => self.eval_storage_read(key, &app_closure, &variable_context),
            Self::Number(numb) => Expr::Number(numb),
        }
    }

    fn op(lhs: Self::Operand, op: Self::Operator, rhs: Self::Operand) -> Self::OpOut {
        match op {
            Op::Add => lhs + rhs,
            Op::Subtract => lhs - rhs,
            Op::Multiply => lhs * rhs,
            Op::Divide => lhs / rhs,
            _ => unreachable!("Pow not supported yet")
        }
    }

}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(init.eval(|_|vec![0x0]), Expr::Number(Number::Float(4.5)));
    }

    #[test]
    fn expr_storage_read() {
        // 1.5 + (GET(_) * 3.0)
        let init = Expr::BinOp { 
            lhs: Box::new(Expr::Number(Number::Float(1.5))), 
            op: Op::Add, 
            rhs: Box::new(Expr::BinOp { 
                lhs: Box::new(
                    // the bytes are irrelevant - we are always returning 5 as the value stored
                    Expr::StorageRead(Key::Bytes(vec![0x0]))),  
                op: Op::Multiply, 
                rhs: Box::new(
                    Expr::Number(Number::Float(3.0))
                ), 
            }) 
        };

        assert_eq!(init.eval(|_| 5u32.to_be_bytes().to_vec()), Expr::Number(Number::Float(16.5)));
    }
}