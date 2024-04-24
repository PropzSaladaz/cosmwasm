use cosmwasm_std::Storage;

use super::super::parser::nodes::*;
use super::eval::{Eval, SEContext};

impl Eval for PathCondition {
    type Output = bool;
    type Operand = Expr;
    type Operator = RelOp;
    type OpOut = bool;

    fn eval(&self, storage: &dyn Storage, variable_context: &SEContext) -> Self::Output 
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
            eval::Eval, path_cond::{Expr, Identifier, Key, Number, PathCondition, RelOp}
        }, 
        testing::mock::*
    };

    use super::Type;


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
        let cond = PathCondition::RelBinOp { 
            lhs: Box::new(Expr::Type(Type::Expr(
                 Box::new(Expr::Identifier(Identifier::Variable("msg".to_owned())))
            ))), 
            rel_op: RelOp::Equal, 
            rhs: Box::new(Expr::MessageType("AddUser".to_owned())) 
        };

        assert!(cond.eval(&storage, &ctx));

        let cond = PathCondition::RelBinOp { 
            lhs: Box::new(Expr::Type(Type::Expr(
                 Box::new(Expr::Identifier(Identifier::Variable("msg".to_owned())))
                ))), 
            rel_op: RelOp::Equal, 
            rhs: Box::new(Expr::MessageType("AddOne".to_owned()))
        };

        assert!(!cond.eval(&storage, &ctx));


        let cond = PathCondition::RelBinOp { 
            lhs: Box::new(Expr::Type(Type::Expr(
                 Box::new(Expr::Identifier(
                                Identifier::AttrAccessor(vec![
                                    "msg".to_owned(),
                                    "balance".to_owned()
                                    ]))))
                )), 
            rel_op: RelOp::Equal, 
            rhs: Box::new(Expr::Type(Type::Expr(
                Box::new(Expr::Number(Number::Int(0))))
                )) 
        };

        assert!(cond.eval(&storage, &ctx));
    }

    #[test]
    fn path_cond_equality() {
        let arg_types = mock_arg_types();
        let ctx = mock_context(&arg_types);
        let storage = mock_storage(HashMap::from([
            (vec![1u8], 1i64.to_le_bytes().to_vec())
        ]));

        // Get(bytes) == Null, when bytes is not in storage
        let cond = PathCondition::RelBinOp { 
            lhs: Box::new(Expr::StorageRead(Key::Bytes(vec![0u8]))), // is not in storage
            rel_op: RelOp::Equal, 
            rhs: Box::new(Expr::Null)
        };

        assert!(cond.eval(&storage, &ctx));

        // Get(bytes) != Null, when bytes is in storage
        let cond = PathCondition::RelBinOp { 
            lhs: Box::new(Expr::StorageRead(Key::Bytes(vec![1u8]))), // is in storage
            rel_op: RelOp::Ne, 
            rhs: Box::new(Expr::Null)
        };

        assert!(cond.eval(&storage, &ctx));

        // msg.balance == 2
        let cond = PathCondition::RelBinOp { 
            lhs: Box::new(Expr::Identifier(Identifier::AttrAccessor(vec![
                "msg".to_owned(),
                "balance".to_owned(),
            ]))), // is in storage
            rel_op: RelOp::Equal, 
            rhs: Box::new(Expr::Number(Number::Int(2)))
        };

        assert!(cond.eval(&storage, &ctx));

        // msg.admin == "name1"
        let cond = PathCondition::RelBinOp { 
            lhs: Box::new(Expr::Identifier(Identifier::AttrAccessor(vec![
                "msg".to_owned(),
                "admin".to_owned(),
            ]))), // is in storage
            rel_op: RelOp::Equal, 
            rhs: Box::new(Expr::String("name1".to_owned()))
        };

        assert!(cond.eval(&storage, &ctx));
    }

    #[test]
    fn path_cond_inequality() {
        let arg_types = mock_arg_types();
        let ctx = mock_context(&arg_types);
        let storage = mock_storage(HashMap::from([
            (vec![1u8], 1i64.to_le_bytes().to_vec())
        ]));
        
        // 1 <= msg.balance
        let cond = PathCondition::RelBinOp {
            lhs: Box::new(Expr::StorageRead(Key::Bytes(vec![1u8]))), // is in storage
            rel_op: RelOp::Lte, 
            rhs: Box::new(Expr::Identifier(Identifier::AttrAccessor(vec![
                "msg".to_owned(),
                "balance".to_owned(),
            ]))),
        };

        assert!(cond.eval(&storage, &ctx));

        // 1 < msg.fee
        let cond = PathCondition::RelBinOp {
            lhs: Box::new(Expr::StorageRead(Key::Bytes(vec![1u8]))), // is in storage
            rel_op: RelOp::Lt, 
            rhs: Box::new(Expr::Identifier(Identifier::AttrAccessor(vec![
                "msg".to_owned(),
                "fee".to_owned(),
            ]))),
        };

        assert!(cond.eval(&storage, &ctx));

        // msg.admin > "n"
        let cond = PathCondition::RelBinOp { 
            lhs: Box::new(Expr::Identifier(Identifier::AttrAccessor(vec![
                "msg".to_owned(),
                "admin".to_owned(),
            ]))),
            rel_op: RelOp::Gt, 
            rhs: Box::new(Expr::String("n".to_owned()))
        };

        assert!(cond.eval(&storage, &ctx));
    }
}