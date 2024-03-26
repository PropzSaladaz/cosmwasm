use super::super::parser::nodes::*;
use super::eval::Eval;

impl Eval for PathCondition {
    type Output = bool;
    type Operand = Expr;
    type Operator = RelOp;
    type OpOut = bool;

    fn eval<F>(self, app_closure: F) -> Self::Output 
    where F: Fn(Key) -> Vec<u8>
    {
        match self {
            Self::RelBinOp { 
                lhs, 
                rel_op, 
                rhs 
            } => match (*lhs, *rhs) {
                ( Expr::Number(a), Expr::Number(b)) 
                => Self::op(Expr::Number(a), rel_op, Expr::Number(b)),

                ( Expr::Number(a), Expr::StorageRead(key) ) 
                => {
                    // TODO EXPLICIT CONVERSION TO INT!!!!! - Assuming everything is int
                    let val = Number::Int(Integer::from_be_bytes(app_closure(key).try_into().unwrap()));
                    Self::op(Expr::Number(a), rel_op, Expr::Number(val))
                }

                ( Expr::StorageRead(key), Expr::Number(a) ) 
                => {
                    // TODO EXPLICIT CONVERSION TO INT!!!!! - Assuming everything is int
                    let val = Number::Int(Integer::from_be_bytes(app_closure(key).try_into().unwrap()));
                    Self::op(Expr::Number(val), rel_op, Expr::Number(a))
                }

                ( Expr::StorageRead(key_a), Expr::StorageRead(key_b) ) 
                => {
                    // TODO EXPLICIT CONVERSION TO INT!!!!! - Assuming everything is int
                    let val_a = Number::Int(Integer::from_be_bytes(app_closure(key_a).try_into().unwrap()));
                    let val_b = Number::Int(Integer::from_be_bytes(app_closure(key_b).try_into().unwrap()));
                    Self::op(Expr::Number(val_a), rel_op, Expr::Number(val_b))
                }
                // TODO No Identifiers supported Yet!                
                expr => unreachable!("Invalid type used for relational operation: {:?}", expr)
            } ,
            Self::Bool(b) => b
        }
    }

    fn op(lhs: Self::Operand, op: Self::Operator, rhs: Self::Operand) -> Self::OpOut {
        match op {
            RelOp::Gte   => lhs >= rhs,
            RelOp::Gt    => lhs > rhs,
            RelOp::Lte   => lhs <= rhs,
            RelOp::Lt    => lhs < rhs,
            RelOp::Equal => lhs == rhs,
            RelOp::Ne    => lhs != rhs,
        }
    }
}