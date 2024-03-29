use super::super::parser::nodes::*;
use super::eval::{Eval, SEContext, StorageAccessor};

impl Eval for PathCondition {
    type Output = bool;
    type Operand = Expr;
    type Operator = RelOp;
    type OpOut = bool;

    fn eval<F: StorageAccessor>(&self, storage: &F, variable_context: &SEContext) -> Self::Output 
    {
        match &self {
            Self::RelBinOp { 
                lhs, 
                rel_op, 
                rhs 
            } => match (&**lhs, &**rhs) {
                (a, b) => {
                    let lhs = a.eval(storage, variable_context);
                    let rhs = b.eval(storage, variable_context);
                    Self::op(&lhs, rel_op, &rhs)
                }
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

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::symb_exec::{
        evaluator::{
            eval::Eval, path_cond::{Expr, Identifier, PathCondition, RelOp}
        }, 
        testing::mock::*
    };


    #[test]
    fn path_cond_true() {
        let arg_types = mock_arg_types();
        let ctx = mock_context(&arg_types);
        let storage = mock_storage(HashMap::new());

        assert!(PathCondition::Bool(true).eval(&storage, &ctx));
    }


    #[test]
    fn path_cond_type() {
        let arg_types = mock_arg_types();
        let ctx = mock_context(&arg_types);
        let storage = mock_storage(HashMap::new());
        // let cond = PathCondition::RelBinOp { 
        //     lhs: Box::new(Expr::Type(
        //          Box::new(Expr::Identifier(
        //                         Identifier::Variable("msg".to_owned())
        //                  ))
        //         )), 
        //     rel_op: RelOp::Equal, 
        //     rhs: Box::new(Expr::Identifier(
        //                         Identifier::Variable("AddUser".to_owned())
        //         )) 
        // };

        // assert!(cond.eval(&storage, &ctx));
    }
}