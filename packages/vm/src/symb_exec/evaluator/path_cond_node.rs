use cosmwasm_std::Storage;

use crate::symb_exec::parser::nodes::PathConditionNode;

use super::eval::{Eval, SEContext};

impl PathConditionNode {
    pub fn parse_tree(&mut self, storage: &dyn Storage, variable_context: &SEContext) -> PathConditionNode
    {
        match self {
            Self::ConditionNode { 
                condition: Some(condition), 
                pos_branch: Some(pos_branch), 
                neg_branch: Some(neg_branch) 
            } => {
                if condition.eval(storage, variable_context) {
                    pos_branch.borrow_mut().parse_tree(storage, variable_context)
                }
                else {
                    neg_branch.borrow_mut().parse_tree(storage, variable_context)
                }
            },
            Self::RWSNode(v) => Self::RWSNode(v.iter_mut().map(|read_write| {
                    read_write.eval(storage, variable_context)}).collect()),
            Self::None => Self::None,
            _ => unreachable!("Expected all ConditionNode optional fields to be Some, but at least 1 was None")
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, collections::HashMap, rc::Rc};

    use crate::symb_exec::{
        evaluator::eval::SEContext, parser::nodes::*, testing::mock::*
    };
    
    fn key_admin() -> Key {
        Key::Expression { 
            base: vec![0u8, 4u8, 98u8, 97u8, 110u8, 107u8], 
            expr: Box::new(Expr::Identifier(Identifier::AttrAccessor(vec![
                "msg".to_owned(), 
                "admin".to_owned()
            ]))) 
        }
    }

    fn key_incr() -> Key {
        Key::Bytes(vec![0u8, 4u8, 98u8, 97u8, 110u8, 107u8, 65u8, 68u8, 77u8, 73u8, 78u8])
    }

    fn build_tree() -> PathConditionNode {
        // [PC_1] Type(_msg) == AddUser
        // => [PC_2]
        // <- [PC_3]

        // [PC_2] GET(=AARiYW5r= @ _msg.admin) == null
        // => SET(=AARiYW5r= @ _msg.admin): 100
        // => GET(=AARiYW5r= @ _msg.admin)
        // <- None

        // [PC_3] Type(_msg) == AddOne
        // => SET(=AARiYW5rQURNSU4=): GET(=AARiYW5rQURNSU4=) + 1
        // => GET(=AARiYW5rQURNSU4=)
        // <- [PC_4]

        // [PC_4] Type(_msg) == Transfer
        // => None
        // <- None

        // [PC_1]
        PathConditionNode::ConditionNode { 

            //  Type(msg) == AddUser
            condition: Some(PathCondition::RelBinOp { 
                lhs: Box::new(Expr::Type(Type::Expr(
                     Box::new(Expr::Identifier(Identifier::Variable("msg".to_owned())))))), 
                rel_op: RelOp::Equal, 
                rhs: Box::new(Expr::Type(Type::Custom("AddUser".to_owned()))) 
            }), 
            // => [PC_2]
            pos_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::ConditionNode { 

                // GET(=AARiYW5r= @ _msg.admin) == null
                condition: Some(PathCondition::RelBinOp { 
                    lhs:  Box::new(Expr::StorageRead(key_admin())), 
                    rel_op: RelOp::Equal, 
                    rhs: Box::new(Expr::Null) 
                }),

                // => SET(=AARiYW5r= @ _msg.admin): Non-Inc
                // => GET(=AARiYW5r= @ _msg.admin)
                pos_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::RWSNode(vec![
                    ReadWrite::Write { 
                        key: key_admin(), 
                        commutativity: WriteType::NonCommutative
                    },
                    ReadWrite::Read(key_admin())
                ]))))), 

                // <- None
                neg_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::None)))) 
            })))), 

            // <- [PC_3]
            neg_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::ConditionNode {

                // Type(msg) == AddOne
                condition: Some(PathCondition::RelBinOp { 
                    lhs: Box::new(Expr::Type(Type::Expr(
                         Box::new(Expr::Identifier(Identifier::Variable("msg".to_owned())))))), 
                    rel_op: RelOp::Equal, 
                    rhs: Box::new(Expr::Type(Type::Custom("AddOne".to_owned()))) 
                }), 
                pos_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::RWSNode(vec![
                    // SET(=AARiYW5rQURNSU4=): Inc
                    // GET(=AARiYW5rQURNSU4=)
                    ReadWrite::Write { 
                        key: key_incr(), 
                        commutativity: WriteType::Commutative
                    },
                    ReadWrite::Read(key_incr())
                ]))))),

                // <- [PC_4]
                neg_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::ConditionNode { 
                    condition: Some(PathCondition::RelBinOp { 
                        lhs: Box::new(Expr::Type(Type::Expr(
                             Box::new(Expr::Identifier(Identifier::Variable("msg".to_owned())))))), 
                        rel_op: RelOp::Equal, 
                        rhs: Box::new(Expr::Type(Type::Custom("Transfer".to_owned()))) 
                    }), 
                    pos_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::None)))), 
                    neg_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::None)))) 
                })))),
            }))))
        }
    }

    // PC_1 true, PC_2 true
    // Type(msg) == AddUSer && 
    // GET(=AARiYW5r @ _msg.admin) == null
    #[test]
    fn parse_pc1_t_pc2_t() {
        let arg_types = mock_arg_types();
        // msg type is "AddUser"
        let ctx = SEContext::new(br#"
            {
                "AddUser": {
                    "admin": "name1"
                }
            }"#,
            &arg_types,
            CosmwasmInputs::Mock
        );

        // set storage empty - when we search for "=AARiYW5r @ _msg.admin" - will return Null
        let storage = mock_storage(HashMap::new());

        // given the initial tree
        let mut node = build_tree();
        
        // get the rws
        let rws = node.parse_tree(&storage, &ctx);

        assert_eq!(rws, PathConditionNode::RWSNode(vec![
            ReadWrite::Write { 
                key: key_admin().eval(&storage, &ctx), 
                commutativity: WriteType::NonCommutative
            },
            ReadWrite::Read(key_admin().eval(&storage, &ctx))
        ]))
    }

    #[test]
    fn parse_pc1_t_pc2_f() {
        // PC_1 true, PC_2 false
        let arg_types = mock_arg_types();
        let ctx = SEContext::new(br#"
            {
                "AddUser": {
                    "admin": "ADMIN"
                }
            }"#,
            &arg_types,
            CosmwasmInputs::Mock
        );

        let storage = mock_storage(HashMap::from([
            // key encoded for "ADMIN"
            (vec![0u8, 4u8, 98u8, 97u8, 110u8, 107u8, 65u8, 68u8, 77u8, 73u8, 78u8], 
             0i64.to_le_bytes().to_vec())
        ]));

        let mut node = build_tree();
        let rws = node.parse_tree(&storage, &ctx);

        assert_eq!(rws, PathConditionNode::None)
    }


    #[test]
    fn parse_pc1_f_pc3_t() {
        // PC_1 false, PC_3 true
        let arg_types = mock_arg_types();

        // PC_1 false - msg type is not AddUser
        // PC_3 true  - msg type is AddOne
        let ctx = SEContext::new(br#"
            {
                "AddOne": {}
            }"#,
            &arg_types,
            CosmwasmInputs::Mock
        );

        let storage = mock_storage(HashMap::from([
            // key encoded for "ADMIN"
            (vec![0u8, 4u8, 98u8, 97u8, 110u8, 107u8, 65u8, 68u8, 77u8, 73u8, 78u8], 
             0i64.to_le_bytes().to_vec())
        ]));

        let mut node = build_tree();
        let rws = node.parse_tree(&storage, &ctx);

        assert_eq!(rws, PathConditionNode::RWSNode(vec![
            ReadWrite::Write { 
                key: key_incr(), 
                commutativity: WriteType::Commutative
            },
            ReadWrite::Read(key_incr())
        ]))
    }

    #[test]
    fn parse_pc1_f_pc3_f_pc4_t() {
        // PC_1 true, PC_2 true
        let arg_types = mock_arg_types();
        let ctx = SEContext::new(br#"
            {
                "Transfer": {}
            }"#,
            &arg_types,
            CosmwasmInputs::Mock
        );

        let storage = mock_storage(HashMap::new());

        let mut node = build_tree();
        let rws = node.parse_tree(&storage, &ctx);

        assert_eq!(rws, PathConditionNode::None);
    }

    #[test]
    fn parse_pc1_f_pc3_f_pc4_f() {
        // PC_1 true, PC_2 true
        let arg_types = mock_arg_types();
        let ctx = SEContext::new(br#"
            {
                "blabla": {}
            }"#,
            &arg_types,
            CosmwasmInputs::Mock
        );

        let storage = mock_storage(HashMap::new());

        let mut node = build_tree();
        let rws = node.parse_tree(&storage, &ctx);

        assert_eq!(rws, PathConditionNode::None);
    }
}   