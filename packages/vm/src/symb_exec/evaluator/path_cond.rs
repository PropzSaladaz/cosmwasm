use super::super::parser::nodes::*;
use super::eval::{Eval, SEContext};

impl Eval for PathCondition {
    type Output = bool;
    type Operand = Expr;
    type Operator = RelOp;
    type OpOut = bool;

    fn eval<F>(&self, app_closure: &F, variable_context: &SEContext) -> Self::Output 
    where F: Fn(&Vec<u8>) -> Vec<u8>
    {
        match &self {
            Self::RelBinOp { 
                lhs, 
                rel_op, 
                rhs 
            } => match (&**lhs, &**rhs) {
                ( Expr::Number(a), Expr::Number(b)) 
                => Self::op(&**lhs, rel_op, &**rhs),

                ( Expr::Number(a), Expr::StorageRead(key) ) 
                => {
                    // TODO EXPLICIT CONVERSION TO INT!!!!! - Assuming everything is int
                    let val = self.eval_storage_read(key, &app_closure, &variable_context);
                    Self::op(&**lhs, rel_op, &val)
                }

                ( Expr::StorageRead(key), Expr::Number(a) ) 
                => {
                    // TODO EXPLICIT CONVERSION TO INT!!!!! - Assuming everything is int
                    let val = self.eval_storage_read(key, &app_closure, &variable_context);
                    Self::op(&val, rel_op, &**rhs)
                }

                ( Expr::StorageRead(key_a), Expr::StorageRead(key_b) ) 
                => {
                    // TODO EXPLICIT CONVERSION TO INT!!!!! - Assuming everything is int
                    let val_a = self.eval_storage_read(key_a, &app_closure, &variable_context);
                    let val_b = self.eval_storage_read(key_b, &app_closure, &variable_context);
                    Self::op(&val_a, rel_op, &val_b)
                }
                // TODO No Identifiers supported Yet!                
                expr => unreachable!("Invalid type used for relational operation: {:?}", expr)
            } ,
            Self::Bool(b) => *b
        }
    }

    fn op(lhs: &Self::Operand, op: &Self::Operator, rhs: &Self::Operand) -> Self::OpOut {
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