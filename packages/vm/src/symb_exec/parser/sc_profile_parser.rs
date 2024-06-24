use std::{
    cell::RefCell, 
    collections::HashMap, 
    fs::File, 
    io::Read, 
    mem, 
    rc::Rc
};
use pest::{
    iterators::{Pair, Pairs}, 
    pratt_parser::{
        self, 
        Assoc::{self}, 
        PrattParser}, 
    Parser
};

use pest_derive::Parser;
use base64::{engine::general_purpose, Engine};

use crate::symb_exec::{se_engine::SEStatus, SEProfile};

use super::nodes::*;


/// Contains all the parsing rules' logic and functionality
#[derive(Parser)]
#[grammar = "symb_exec/parser/symb_exec.pest"]
pub struct SEParser;

#[derive(Debug, PartialEq)]
pub struct SCProfile {
    pub status: SEStatus,
    pub entry_point: HashMap<EntryPoint, EntryPointProfile>,
}

impl SCProfile {
    pub fn new(status: SEStatus) -> Self {
        SCProfile { 
            status: status,
            entry_point: HashMap::new() 
        }
    }

    pub fn add_entry_point_profile(&mut self, entry_point: EntryPoint, profile: EntryPointProfile) {
        self.entry_point.insert(entry_point, profile);
    }
}

pub struct SCProfileParser {
    /// Parser used to parse expressions taking into account
    /// operation associativity
    pratt_parser: PrattParser<Rule>,

    /// Final SCProfile structure, holding all relevant data
    sc_profile: SCProfile, // TODO pub just to test in prints

    /// Works as state machine to set the current section
    /// while parsing
    current_entry_point: Option<EntryPoint>,
    current_entry_point_profile: EntryPointProfile,
}

impl SCProfileParser {

    fn new(status: SEStatus) -> Self {
        SCProfileParser {
            pratt_parser: PrattParser::new()
            .op(pratt_parser::Op::infix(Rule::add, Assoc::Left) | pratt_parser::Op::infix(Rule::sub, Assoc::Left))
            .op(pratt_parser::Op::infix(Rule::mul, Assoc::Left) | pratt_parser::Op::infix(Rule::div, Assoc::Left))
            .op(pratt_parser::Op::infix(Rule::pow, Assoc::Right))
            .op(pratt_parser::Op::prefix(Rule::neg)),

            sc_profile: SCProfile::new(status),

            current_entry_point: None,
            current_entry_point_profile: EntryPointProfile::new(),
        }
    }

    fn set_entry_profile_for_current_entry_point(&mut self) {
        // move values from struct fields - need to use mem::replace
        let entry_point = mem::replace(&mut self.current_entry_point, None);
        let current_entry_point_profile = 
            mem::replace(&mut self.current_entry_point_profile, EntryPointProfile::new());
        self.sc_profile.add_entry_point_profile(
            entry_point.unwrap(),
            current_entry_point_profile);
    }

    /// Parses a well-formated SE-output file into an internal in-memory representation of
    /// both the Inputs, Offsets, and RWS tree.
    /// 
    /// The tree can then be parsed at runtime with some specific values to compute the 
    /// actual value.
    pub fn from_file(status: SEStatus, file_path: &str) -> SCProfile {
        let mut file = File::open(file_path).expect("Could not open SE file");
        let mut contents = String::new();
        file.read_to_string(&mut contents).expect("Could not read file into string");
        SCProfileParser::from_string(status, contents)
    }

    pub fn from_se_profile(se_profile: SEProfile) -> SCProfile {
        SCProfileParser::from_string(se_profile.status, se_profile.profile)
    }

    pub fn from_string(status: SEStatus, contents: String) -> SCProfile {
        let mut parser = SCProfileParser::new(status);

        let main = SEParser::parse(Rule::main, contents.as_str())
            .expect("Could not parse SE content - check if SE is well formatted!");
        let sections = main.into_iter().next().unwrap();
        
        for section in sections.into_inner() {
            for subsection in section.into_inner() {
                match subsection.as_rule() {
                    Rule::header    => { parser.parse_header   (subsection); },
                    Rule::inputs    => { parser.parse_inputs   (subsection); },
                    Rule::attr_defs => { parser.parse_attr_defs(subsection); },
                    Rule::path_cond_nodes => {
                        parser.parse_path_cond_nodes(subsection);
                        parser.set_entry_profile_for_current_entry_point(); // only set at the end of parsing current section
                    },
                    rule => unreachable!("Expected a subsection, found {:?}", rule),
                }
            }
        };
        parser.sc_profile
    }

    pub fn parse_header(&mut self, header: Pair<Rule>) {
        let entry_point = match header.into_inner().next().unwrap().as_rule() {
            Rule::instantiate   => EntryPoint::Instantiate,
            Rule::execute       => EntryPoint::Execute,
            Rule::query         => EntryPoint::Query,
            rule => unreachable!("Expected a section_type, found {:?}", rule),
        };

        self.current_entry_point = Some(entry_point);
        self.current_entry_point_profile = EntryPointProfile::new();
    }

    pub fn parse_inputs(&mut self, inputs: Pair<Rule>) {
        for input in inputs.into_inner() {
            let mut inner = input.into_inner();     
            let identifier = inner.next().unwrap().as_str();        // get input variable name

            let input_type = match inner.next().unwrap().as_rule() {
                Rule::deps_mut  => InputType::DepsMut,
                Rule::env       => InputType::Env,
                Rule::msg_info  => InputType::MessageInfo,
                _               => InputType::Custom,
            };
            self.current_entry_point_profile.add_input(identifier, input_type);
        }
    }

    pub fn parse_attr_defs(&mut self, attr_defs: Pair<Rule>) {
        for offset in attr_defs.into_inner() {       // attr_def: { rust_id ~ attr_def* }

            let mut inner = offset.into_inner();       // rust_id ~ subtype_def*
            let msg_type = inner.next().unwrap().as_str();        // rust_id

            self.current_entry_point_profile.add_custom_input_msg_variant(msg_type);
            
            for offset_definition in  inner {           // subtype_def: { rust_id ~ type }
                
                let mut inner = offset_definition.into_inner();         // rust_id ~ type
                let field_id = inner.next().unwrap().as_str();                     // rust_id

                let type_def = inner.next().unwrap();    // type
                let ty = match type_def.as_rule() {
                    Rule::string_t => Type::String,
                    Rule::int_t => Type::Int,
                    Rule::float_t => Type::Float,
                    r => unreachable!("expecting a {{string,int,float}}_t, found {:?}", r)
                };

                self.current_entry_point_profile.add_field_def_for_msg_variant(
                    msg_type, 
                    field_id, 
                    ty);
            }
        }
    }

    /// Parses all path conditions for some entry point. 
    /// Uses a HashMap to store temporarily all parsed path conditions by ID, while building the 
    /// binary tree at the same time.
    /// 
    /// Assumes path conditions are always referenced by their parent before they appear in the file.
    /// Meaning PC_2 only appears after being used as either a positive or negative path for a previous
    /// path, say PC_1.
    pub fn parse_path_cond_nodes(&mut self, path_cond_nodes: Pair<Rule>) {
        use super::nodes::TransactionDependency::*;

        let mut tmp_path_cond: HashMap<i32, CondNodeRef> = HashMap::new();

        for path_cond_node in path_cond_nodes.into_inner() { // { path_cond ~ pos_branches ~ neg_branches }
            let mut inner = path_cond_node.into_inner();    // path_cond ~ pos_branches ~ neg_branches

            // Parse path_id and path condition first
            let mut path_cond = inner.next().unwrap().into_inner(); // path_cond: { path_cond_id ~ bool_expr }
            let id: i32 = path_cond.next().unwrap() // path_cond_id: { int }
                .into_inner().as_str().parse().unwrap();          // int
            let bool_expr = self.parse_bool_expr(path_cond.next().unwrap()); // bool_expr
            let curr_node;

            // If path_id has already been inserted in tmp map
            if let Some(node) = tmp_path_cond.get_mut(&id) {
                curr_node = node.clone();
                match &mut curr_node.try_borrow_mut().unwrap().as_mut() {
                    PathConditionNode::ConditionNode { 
                        condition, 
                        .. 
                    } => *condition = Some(bool_expr),
                    rule => unreachable!("Expected ConditionNode, found {:?}", rule),
                };
            // first node
            } else {
                curr_node = Rc::new(RefCell::new(Box::new(PathConditionNode::ConditionNode { 
                    storage_dependency: INDEPENDENT,
                    condition: Some(bool_expr), 
                    pos_branch: None, 
                    neg_branch: None 
                })));
                tmp_path_cond.insert(id, curr_node.clone());
                // set root node
                self.current_entry_point_profile.set_root_path_cond(curr_node);
            }


            // Parse positive branch(es)
            let pos_branches = inner.next().unwrap();
            let rule = pos_branches.as_rule();
            self.parse_branches(id, &mut tmp_path_cond, &mut pos_branches.into_inner(),
            rule);

            // Parse negative branch(es)
            let neg_branches = inner.next().unwrap();
            let rule = neg_branches.as_rule();
            self.parse_branches(id, &mut tmp_path_cond, &mut neg_branches.into_inner(),
            rule);
        }
    }


    fn parse_branches(&self, id: i32, tmp_path_cond: &mut HashMap<i32, Rc<RefCell<Box<PathConditionNode>>>>, 
        branches: &mut Pairs<Rule>, branch_type: Rule) {
        use super::nodes::TransactionDependency::*; 

        // ------------- Helper Functions ------------ //
        
        // Helper function to parse storage writes
        let parse_storage_write = |write: Pair<Rule>| {
            let mut storage_write =  write.into_inner();
            let key = self.parse_storage_key(storage_write.next().unwrap());
            match storage_write.next().unwrap().into_inner().next().unwrap().as_rule() {
                // We mark all RWS as storage independent here, but later we evaluate them and may change them to DEPENDENT
                Rule::incremental     => ReadWrite::Write { storage_dependency: INDEPENDENT, key, commutativity: WriteType::Commutative },
                Rule::non_incremental => ReadWrite::Write { storage_dependency: INDEPENDENT, key, commutativity: WriteType::NonCommutative },
                other           => unreachable!("Expected write type, got {:?}", other)
            }
            
        };

        // Helper function to parse storage reads
        let parse_storage_read = |read: Pair<Rule>| {
            let mut storage_read =  read.into_inner();
            let key = self.parse_storage_key(storage_read.next().unwrap());
            match storage_read.next().unwrap().into_inner().next().unwrap().as_rule() {
                // We mark all RWS as storage independent here, but later we evaluate them and may change them to DEPENDENT
                Rule::incremental     => ReadWrite::Read { storage_dependency: INDEPENDENT, key, commutativity: WriteType::Commutative },
                Rule::non_incremental => ReadWrite::Read { storage_dependency: INDEPENDENT, key, commutativity: WriteType::NonCommutative },
                other           => unreachable!("Expected read type, got {:?}", other)
            }
        };

        // Helper function to set child path condition branch. It captures the current branch type from the current function's
        // context, and adds the pathConditionBranch passed to the correct Positive or Negative child.
        let mut set_child_branch_for_curr_node = |path_cond_node: Rc<RefCell<Box<PathConditionNode>>>| {
            tmp_path_cond.entry(id).and_modify(|path_cond: &mut Rc<RefCell<Box<PathConditionNode>>>| {
                match &mut (**path_cond.borrow_mut()) {
                    PathConditionNode::ConditionNode { 
                        pos_branch,
                        neg_branch,
                        .. 
                    } => {
                        let path_cond_node = Some(path_cond_node);
                        match branch_type {
                            Rule::pos_branches => *pos_branch = path_cond_node,
                            Rule::neg_branches => *neg_branch = path_cond_node,
                            rule => unreachable!("Expected positive or negative branch, found {:?}", rule),
                        }
                    }
                    rule => unreachable!("Expected ConditionNode, found {:?}", rule),
                }
            });
        };

        // ------------- Main Logic ------------ //
        // get 1st element to check which type it is
        match branches.clone().next().unwrap().as_rule() {

            // If 1st element is read or write -> all following elements must be also read/write
            Rule::storage_read | 
            Rule::storage_write 
            => {                       
                let mut write_set: Vec<ReadWrite> = Vec::new();

                // Run over all RWS
                for branch_data in branches {
                    let read_write: ReadWrite = match branch_data.as_rule() {
                        Rule::storage_write => parse_storage_write(branch_data),
                        Rule::storage_read  => parse_storage_read(branch_data),
                        rule => unreachable!("Expected read or write, found {:?}", rule)
                    };
                    write_set.push(read_write);
                };
    
                // Update child branch in current path_cond_node with the RWS - detects 
                // automatically the type of child branch (positive vs. negative)
                set_child_branch_for_curr_node(
                    Rc::new(RefCell::new(Box::new(PathConditionNode::RWSNode {
                        storage_dependency: INDEPENDENT,
                        rws: write_set 
                    }))));
            },

            // If 1st element is path_cond_id or None -> Child branch will never be read/write
            Rule::none | 
            Rule::path_cond_id 
            => {
                let branch_data = branches.next().unwrap();
                match branch_data.as_rule() {
                    Rule::none          => set_child_branch_for_curr_node(
                        Rc::new(RefCell::new(Box::new(PathConditionNode::None)))),
                    Rule::path_cond_id  => {
                        let child_id: i32 = branch_data.into_inner().next().unwrap().as_str().parse().unwrap();

                        // init mock & reference it as a child path. When we parse this we fill it with data
                        let new_cond_node = 
                            Rc::new(RefCell::new(Box::new(PathConditionNode::ConditionNode { 
                                storage_dependency: INDEPENDENT,
                                condition: None, 
                                pos_branch: None, 
                                neg_branch: None, 
                            })));
                        set_child_branch_for_curr_node(new_cond_node.clone());
                        // Store in hashmap, so that we can parse it and fill it with data from the SE output
                        tmp_path_cond.insert(child_id, new_cond_node.clone());
                    },
                    rule => unreachable!("Expected either storage_write, none, or path_cond_id. Found {:?}", rule),
                }
            },
            rule => unreachable!("Expected path_data, found {:?}", rule)
        }
    }

    fn parse_bool_expr(&self, bool_expr: Pair<Rule>) -> PathCondition {
        let bool_inner = bool_expr.into_inner().next().unwrap();
        
        match bool_inner.as_rule() {
            Rule::always_true => PathCondition::Result{ storage_dependency: TransactionDependency::INDEPENDENT, satisfied: true },
            Rule::rel_expr => {
                let expr_inner = bool_inner.into_inner().next().unwrap();
                match expr_inner.as_rule() {
                    Rule::comparison => {
                        let mut expr_inner = expr_inner.into_inner();
                        let expr_l = self.parse_expr(expr_inner.next().unwrap().into_inner());
                        let rel_op = match expr_inner.next().unwrap().as_rule() {
                            Rule::gte   => RelOp::Gte,
                            Rule::lte   => RelOp::Lte,
                            Rule::equal => RelOp::Equal,
                            Rule::ne    => RelOp::Ne,
                            Rule::lt    => RelOp::Lt,
                            Rule::gt    => RelOp::Gt,
                            rule => unreachable!("Expected rel_operator, found {:?}", rule),
                        };

                        let expr_r_tmp = expr_inner.next().unwrap();
                        let expr_r = match expr_r_tmp.as_rule() {
                            Rule::expr => self.parse_expr(expr_r_tmp.into_inner()),
                            Rule::null => Expr::Null,
                            rule => unreachable!("Expecting expr or null, got {:?}", rule)
                        };
        
                        PathCondition::RelBinOp { lhs: Box::new(expr_l), rel_op: rel_op, rhs: Box::new(expr_r) }
                    },
                    
                    // When checking type, currently only supports expressions of the following structure:
                    // Type(msg) == SomeType
                    Rule::type_checking => {
                        let mut expr_inner = expr_inner.into_inner();
                        let expr_l = self.parse_type(expr_inner.next().unwrap().into_inner().next().unwrap());
                        let rel_op = match expr_inner.next().unwrap().as_rule() {
                            Rule::equal => RelOp::Equal,
                            Rule::ne    => RelOp::Ne,
                            rule => unreachable!("Expected equality operator, found {:?}", rule),
                        };
                        let expr_r = Expr::MessageType(expr_inner.next().unwrap().as_str().to_owned());
                        PathCondition::RelBinOp { lhs: Box::new(expr_l), rel_op: rel_op, rhs: Box::new(expr_r) }
                    },
                    rule => unreachable!("Expected comparison or type_checking, got {:?}", rule),
                }

            },
            rule => unreachable!("Expected rel_expr or always_true, found {:?}", rule),
        }
    }

    /// Parses a "type" expression:
    /// 
    /// `Type(something) == ...``
    /// 
    /// Where something can be either a single variable identifier - `msg` - or an attribute accessor - `msg.a.b`
    /// If `msg` is any of the inputs, set it as `MessageType`, else set it as `Identifier`.
    /// Then set the inner Identifier as `AttributeAccessor` or `Variable` depending on the type.
    fn parse_type(&self, variable: Pair<Rule>) -> Expr {
        let var_str = String::from(variable.clone().as_str());
        Expr::Type(Type::Expr(Box::new(match variable.clone().as_rule() {
            Rule::rust_identifier => Expr::Identifier(Identifier::Variable(var_str)),
            Rule::attr_accessor => {
                let mut tokens = vec![];
                for token in variable.into_inner() {
                    tokens.push(String::from(token.as_str()));
                };
                Expr::Identifier(Identifier::AttrAccessor(tokens))
            },
            other => unreachable!("Expected rust_identifier or attr_accessor, found {:?}", other),
        })))
    }

    fn parse_storage_key(&self, key: Pair<Rule>) -> Key {
        let mut base = Vec::new();
        let inner = key.into_inner();
        for content in inner {
            match content.as_rule() {
                Rule::base64 => {
                    let base64_str = content.as_str();
                    base = general_purpose::STANDARD.decode(base64_str)
                        .expect("Could not decode base64 from SE output");
                },
                Rule::expr => {
                    return Key::Expression { 
                        base: base, 
                        expr: Box::new(self.parse_expr(content.into_inner())) 
                    }
                },
                _ => unreachable!(),
            };
        }
        Key::Bytes(base)

    }

    fn parse_expr(&self, pairs: Pairs<Rule>) -> Expr {
        use Number::*;

        self.pratt_parser
        .map_primary(|primary| match primary.as_rule() { // parse atomic tokens
            Rule::int           => Expr::Number(Int(primary.as_str().parse().unwrap())),
            Rule::float         => Expr::Number(Float(primary.as_str().parse().unwrap())),
            Rule::cond_storage_read  => {
                let key_pair = primary.into_inner().next().unwrap();
                let key: Key = self.parse_storage_key(key_pair);
                Expr::StorageRead(key)
            },
            Rule::variable      => {
                let inner = primary.into_inner().next().unwrap();
                match &inner.as_rule() {
                    Rule::attr_accessor => {
                        let mut tokens = vec![];
                        // check if variable is a single variable or an attribute accessor
                        for token in inner.into_inner() {
                            tokens.push(token.as_str().to_owned());
                        }
                        Expr::Identifier(Identifier::AttrAccessor(tokens))
                    }
                    Rule::rust_identifier => {
                        let id = inner.into_inner().next().unwrap().as_str().to_owned();
                        if self.current_entry_point_profile.is_custom_subtype(&id) {
                            // Used to specify that the current variable represents a type
                            // Type(msg) == AddOne -> Here AddOne will be a MessageType 
                            Expr::MessageType(id)
                        }
                        else {
                            Expr::Identifier(Identifier::Variable(id))
                        }
                    },
                    other => unreachable!("Expected attr_accessor or rust_identifier, got {:?}", other)
                }
            },
            Rule::expr          => self.parse_expr(primary.into_inner()), // from "(" ~ expr ~ ")"
            rule          => unreachable!("Expected a primary, found {:?}", rule),

        })
        .map_prefix(|op, rhs| match op.as_rule() {
            Rule::neg  => match rhs {
                Expr::Number(Int(val)) => Expr::Number(Int(-val)),
                Expr::Number(Float(val)) => Expr::Number(Float(-val)),
                rule => unreachable!("parse_exrp expected Int or Float, found {:?}", rule), // TODO currently no support for unary operations besides for floats & ints
            },
            rule          => unreachable!("Expected a prefix, found {:?}", rule),

        })
        .map_infix(|lhs, op, rhs| {
            let op = match op.as_rule() {
                Rule::add => Op::Add,
                Rule::sub => Op::Subtract,
                Rule::mul => Op::Multiply,
                Rule::div => Op::Divide,
                Rule::pow => Op::Power,
                rule => unreachable!("parse_expr expected infix operation, found {:?}", rule),
            };
            Expr::BinOp {
                lhs: Box::new(lhs),
                op,
                rhs: Box::new(rhs),

            }
        })
        .parse(pairs)
    }
}


#[cfg(test)]
mod tests {
    use crate::symb_exec::EntryPoint;
    use super::super::nodes::TransactionDependency::*;
    use super::*;

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

    #[test]
    fn parse_se_output() {
        let s = String::from("E ----------------------------
_deps: DepsMut
_env: Env
_info: MessageInfo
msg: ExecuteMsg
> AddUser:
	- admin: string
> AddOne:
> Transfer:
	- from: string
	- to: string


[PC_1] Type(msg) == AddUser
=> [PC_2]
<- [PC_3]

[PC_2] GET(=AARiYW5r @ msg.admin) == null
=> GET(=AARiYW5r @ msg.admin): Non-Inc
=> SET(=AARiYW5r @ msg.admin): Non-Inc
<- None

[PC_3] Type(msg) == AddOne
=> GET(=AARiYW5rQURNSU4=): Inc
=> SET(=AARiYW5rQURNSU4=): Inc
<- [PC_4]

[PC_4] Type(msg) == Transfer
=> None
<- None");

    let profile = SCProfileParser::from_string(SEStatus::Complete, s);


    let cond_node = Rc::new(RefCell::new(Box::new(PathConditionNode::ConditionNode { 
        storage_dependency: INDEPENDENT,
        //  Type(msg) == AddUser
        condition: Some(PathCondition::RelBinOp { 
            lhs: Box::new(Expr::Type(Type::Expr(
                 Box::new(Expr::Identifier(Identifier::Variable("msg".to_owned())))
            ))), 
            rel_op: RelOp::Equal, 
            rhs: Box::new(Expr::MessageType("AddUser".to_owned())) 
        }), 
        // => [PC_2]
        pos_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::ConditionNode { 
            storage_dependency: INDEPENDENT,
            // CONDITION
            // GET(=AARiYW5r= @ _msg.admin) == null
            condition: Some(PathCondition::RelBinOp { 
                lhs:  Box::new(Expr::StorageRead(key_admin())), 
                rel_op: RelOp::Equal, 
                rhs: Box::new(Expr::Null) 
            }),

            // RWS
            // => GET(=AARiYW5r= @ _msg.admin): Non-Inc
            // => SET(=AARiYW5r= @ _msg.admin): Non-Inc
            pos_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::RWSNode {
                storage_dependency: INDEPENDENT,
                rws: vec![
                ReadWrite::Read {
                    storage_dependency: INDEPENDENT,
                    key: key_admin(),
                    commutativity: WriteType::NonCommutative,
                },
                ReadWrite::Write { 
                    storage_dependency: INDEPENDENT,
                    key: key_admin(), 
                    commutativity: WriteType::NonCommutative
                },
            ]})))), 

            // <- None
            neg_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::None)))) 
        })))), 

        // <- [PC_3]
        neg_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::ConditionNode {
            storage_dependency: INDEPENDENT,
            // CONDITION
            // Type(msg) == AddOne
            condition: Some(PathCondition::RelBinOp { 
                lhs: Box::new(Expr::Type(Type::Expr(Box::new(
                     Expr::Identifier(Identifier::Variable("msg".to_owned())))
                ))), 
                rel_op: RelOp::Equal, 
                rhs: Box::new(Expr::MessageType("AddOne".to_owned())) 
            }), 
            pos_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::RWSNode {
                storage_dependency: INDEPENDENT,
                rws: vec![
                
                // RWS
                // SET(=AARiYW5rQURNSU4=): Inc
                // GET(=AARiYW5rQURNSU4=): Inc
                ReadWrite::Read{
                    storage_dependency: INDEPENDENT,
                    key: key_incr(),
                    commutativity: WriteType::Commutative,
                },
                ReadWrite::Write { 
                    storage_dependency: INDEPENDENT,
                    key: key_incr(), 
                    commutativity: WriteType::Commutative
                },
            ]})))),

            // <- [PC_4]
            neg_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::ConditionNode { 
                storage_dependency: INDEPENDENT,
                condition: Some(PathCondition::RelBinOp { 
                    lhs: Box::new(Expr::Type(Type::Expr(Box::new(
                         Expr::Identifier(Identifier::Variable("msg".to_owned())))
                    ))), 
                    rel_op: RelOp::Equal, 
                    rhs: Box::new(Expr::MessageType("Transfer".to_owned())) 
                }), 
                pos_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::None)))), 
                neg_branch: Some(Rc::new(RefCell::new(Box::new(PathConditionNode::None)))) 
            })))),
        }))))
    })));

    assert_eq!(
        profile.entry_point.get(&EntryPoint::Execute).unwrap().root_path_cond.as_ref().unwrap(),
        &cond_node
    );


    }
}