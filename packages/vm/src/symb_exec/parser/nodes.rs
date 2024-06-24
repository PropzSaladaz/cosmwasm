use std::{cell::RefCell, collections::HashMap, rc::Rc};
use std::ops::Not;
use cosmwasm_std::{Env, MessageInfo};
use num::traits::ToBytes;
use serde::Serialize;

use crate::DepsMut;

pub type Float = f64;
pub type Integer = i64;

#[derive(Debug, Copy, Clone, Serialize)]
pub enum Number {
    Float(Float),
    Int(Integer),
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Identifier {
    Variable(String),
    // attribute accessors - var1.field1 will be represented
    // as vec["var1", "field1"]
    AttrAccessor(Vec<String>),
}

/// Represents arithmetic binary operators
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Op {
    Add,
    Subtract,
    Multiply,
    Divide,
    Power
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Type {
    String,
    Float,
    Int,
    Custom(String),
    Expr(Box<Expr>),
}

/// Represents a arithmetic expression. Can be defined recursively, and
/// when parsed, will respect associativity rules.
/// 
/// When defined as BinOp, can only use arithmetic operations (+, -, /, *)
#[derive(Debug, Clone, Serialize)]
pub enum Expr {
    /// Used to define enum matching for the custom message type
    /// we currently only allow Type(x) on as the left-hand side
    /// if x is a custom msg. We use it to decide the actual type of msg
    /// it is - `Type(msg) == AddUSer`, `AddOne`, etc...
    /// 
    /// `MessageType(X)` - X represents the right side, i.e, `AddUser`, `AddOne`, etc
    MessageType(String),

    Identifier(Identifier),
    StorageRead(Key),
    Number(Number),
    String(String),
    Null,

    // generic type - can be used for attribute accessors, expressions, etc
    // and evaluates to primitive types - Number/String
    Type(Type), 
    
    BinOp {
        lhs: Box<Expr>,
        op: Op,
        rhs: Box<Expr>,
    },

    Result {
        expr: Box<Expr>,
        dependency: TransactionDependency,
    },
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq)]
pub enum TransactionDependency {
    DEPENDENT,
    INDEPENDENT
}

use std::ops::BitOr;

impl BitOr for TransactionDependency {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (TransactionDependency::DEPENDENT, _) | (_, TransactionDependency::DEPENDENT) => TransactionDependency::DEPENDENT,
            (TransactionDependency::INDEPENDENT, TransactionDependency::INDEPENDENT) => TransactionDependency::INDEPENDENT,
        }
    }
}

/// Represents the result of parsing an expression. If an expression in a condition 
/// depends on a read from store, then that expression is marked as DEPENDENT as it
/// depends on state, meaning the RWS may change during execution.
#[derive(Debug, Clone, Serialize)]
pub struct ExprRes {
    pub expression: Expr, 
    pub dependency: TransactionDependency,
}

impl Expr {
    pub fn as_bytes(&self) -> Option<Vec<u8>> {
        match self {
            Expr::Number(n) => match n {
                Number::Int(i) => Some(i.to_le_bytes().to_vec()),
                Number::Float(f) => Some(f.to_le_bytes().to_vec()),
            },
            Expr::String(s) => unsafe { Some(s.clone().as_mut_vec().to_vec()) },
            Expr::Result { expr, dependency: _ } => expr.as_bytes(),
            _ => None,
        }
    }
}

/// Represents different Smart Contract entry points
#[derive(Debug, PartialEq, Eq, Hash, Serialize)]
pub enum EntryPoint {
    Instantiate,
    Execute,
    Query,
    Reply,
}

/// Represents all possible pre-defined input types, and also 
/// a Custom type for the SC's custom messages
#[derive(Debug, PartialEq, Eq, Hash, Serialize)]
pub enum InputType {
    DepsMut,
    Env,
    MessageInfo,
    Custom,
}

/// Used to store the inputs received as arguments for each entry point
/// so that they may be used when evaluating a profile tree
pub enum CosmwasmInputs<'a> {
    Instantiate {
        deps:   &'a DepsMut<'a>,
        env:    &'a Env,
        info:   &'a MessageInfo,
    },
    Execute {
        deps:   &'a DepsMut<'a>,
        env:    &'a Env,
        info:   &'a MessageInfo
    },
    Query {
        deps:   &'a DepsMut<'a>,
        env:    &'a Env,
    },
    Mock
}

#[derive(Debug)]
pub enum TypeDepsMut {
    Storage,
    Api,
    Querier, // TODO - IMPORTANT! - Must define also the pub functions of querier!!
}

#[derive(Debug)]
pub enum TypeEnv {
    // TODO - IMPORTANT! - Must define all public fields and methods!!
}

#[derive(Debug)]
pub enum TypeMessageInfo {
    // TODO - IMPORTANT! - Must define all public fields and methods!!
}

/// Represents all relational operators: >=, <=, ==, !=, <, > 
#[derive(Debug, PartialEq, Serialize)]
pub enum RelOp {
    Gte,
    Lte,
    Equal,
    Ne,
    Lt,
    Gt,
}

/// Represents a path condition.
/// Is either always True, or is a comparison between 2 expressions
#[derive(Debug, PartialEq, Serialize)]
pub enum PathCondition {
    Result {
        storage_dependency: TransactionDependency,
        satisfied: bool,
    },
    RelBinOp {
        lhs: Box<Expr>,
        rel_op: RelOp,
        rhs: Box<Expr>,
    }
}


/// Represents a storage key. 
/// Can either be represented in Bytes if the SE-output is in base64,
/// or in the form of an expression otherwise to be computed at runtime.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Key {
    Bytes(Vec<u8>),
    Expression {
        base: Vec<u8>,
        expr: Box<Expr>,
    }, 
}

#[derive(Debug, Copy, Clone, PartialEq, Serialize)]
pub enum WriteType {
    Commutative,
    NonCommutative
}

/// Represents either a read or write to be stored as a RWS
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ReadWrite {
    Write {
        storage_dependency: TransactionDependency,
        key: Key,
        commutativity: WriteType,
    },


    /// Read commutativity refers to if a read is solely associated
    /// to a commutative write.
    /// If we have W(A): R(A) + 1, then this read will appear before 
    /// the write, and since the write is commutative, the read will
    /// also be marked as commutative.
    /// It is important to mark every read and its commutativity because
    /// the algorithm that identifies the store items to partition will
    /// ignore commutative reads, since it will already consider the respective
    /// commutative write.
    Read {
        storage_dependency: TransactionDependency,
        key: Key,
        commutativity: WriteType,
    },
}

impl Default for ReadWrite {
    fn default() -> ReadWrite {
        Self::Read {
            storage_dependency: TransactionDependency::INDEPENDENT,
            key: Key::Bytes(vec![0]),
            commutativity: WriteType::NonCommutative
        }
    }
}

// Rc for shared access to reference -> 
// RefCell for mutating the inner data -> 
// Box needed since it's recursive
pub type CondNodeRef = Rc<RefCell<Box<PathConditionNode>>>;
/// Represents a node in the path condition tree.
/// 
/// Each node has 1 condition and at least 1 positive and 1 negative branch.
/// 
/// If the node has information about the RWS, then it can have >1 child branches (positive/negative)
#[derive(Debug, PartialEq)]
pub enum PathConditionNode {
    /// Represents a full node associated to a condition, and both child branches.
    ConditionNode {
        storage_dependency: TransactionDependency,
        /// Represents the boolean condition
        condition: Option<PathCondition>,
        
        pos_branch: Option<CondNodeRef>,
        neg_branch: Option<CondNodeRef>,
    },
    // TODO - currently we only store gets that are not issued to the same position 
    // as the write (and that appear as a dependency for that write)
    /// Represents the RWS under a specific child branch (positive / negative)
    RWSNode {
        storage_dependency: TransactionDependency,
        rws: Vec<ReadWrite>,
    },
    None,
}


pub type ArgTypes = HashMap<String, InputType>;
pub type CustomArgTypes = HashMap<String, HashMap<String, Type>>;

/// Represents all info related to each entry point:
/// 
/// Inputs, type_defs, and Path conditions (RWS)
#[derive(Debug, PartialEq)]
pub struct EntryPointProfile {
    /// Maps all input variable names to their types.
    /// 
    ///  _msg -> Custom
    ///  
    ///  _deps -> DepsMut
    /// 
    /// 
    pub inputs: ArgTypes,
    
    /// Stores type_defs for each atribute within each custom message type:
    /// 
    ///   struct AddUSer {
    ///     field1: String,
    ///     field2: String 
    ///   }
    /// 
    /// 
    /// These type_defs refer only to the input variable of type Custom
    pub type_defs: CustomArgTypes,

    /// Root condition node in the tree
    pub root_path_cond: Option<CondNodeRef>,
}

impl EntryPointProfile {
    pub fn new() -> Self {
        Self {
            inputs: HashMap::new(),
            type_defs: HashMap::new(),
            root_path_cond: None,
        }
    }

    pub fn add_input(&mut self, identifier: &str, input_type: InputType) {
        self.inputs.insert(String::from(identifier), input_type);
    }

    /// Adds a message variant for the custom input field.
    /// 
    /// In cosmwasm, messages are matched by their type, which is up to the user to define:
    /// 
    /// ```
    /// enum Executemsg { 
    /// 
    ///     AddUser, 
    ///     DoSomething {
    ///         a: i32,
    ///         b: i32,
    ///     }, 
    ///     RemoveUser { user: String } 
    /// 
    /// }
    /// ```
    /// 
    /// This stores the message variants (AddUser, DoSomething, RemoveUser) as well as the type_defs
    /// for the variants that have further fields (e.g. RemoveUser.user)
    pub fn add_custom_input_msg_variant(&mut self, attr_id: &str) {
        self.type_defs.entry(String::from(attr_id)).or_insert(HashMap::new());
    }

    pub fn add_field_def_for_msg_variant(&mut self, attr_id: &str, field_id: &str, ty: Type) {
        self.type_defs.entry(String::from(attr_id)).and_modify(|type_defs| {
            type_defs.entry(String::from(field_id)).or_insert(ty);
        });
    }

    pub fn set_root_path_cond(&mut self, root_path_cond: Rc<RefCell<Box<PathConditionNode>>>) {
        self.root_path_cond = Some(root_path_cond);
    }

    pub fn is_custom_subtype(&self, var_name: &String) -> bool {
        return self.type_defs.contains_key(var_name);
    }

    pub fn is_input_argument(&self, var_name: &String) -> bool {
        self.inputs.contains_key(var_name)
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expr_as_bytes() {
        let expr = Expr::Number(Number::Int(1000));
        assert_eq!(expr.as_bytes(), Some((1000 as Integer).to_le_bytes().to_vec()));

        let expr = Expr::Number(Number::Float(2.654));
        assert_eq!(expr.as_bytes(), Some((2.654 as Float).to_le_bytes().to_vec()));

        let expr = Expr::String(String::from("Hey man"));
        assert_eq!(expr.as_bytes(), Some(b"Hey man".to_vec()));

        let expr = Expr::Identifier(Identifier::AttrAccessor(vec![]));
        assert_eq!(expr.as_bytes(), None);

        let expr = Expr::MessageType("abc".to_owned());
        assert_eq!(expr.as_bytes(), None);
    }
}