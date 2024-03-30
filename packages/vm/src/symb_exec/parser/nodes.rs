use std::{cell::RefCell, collections::HashMap, rc::Rc};

use num::traits::ToBytes;

pub type Float = f64;
pub type Integer = i64;

#[derive(Debug, Copy, Clone)]
pub enum Number {
    Float(Float),
    Int(Integer),
}

#[derive(Debug, Clone)]
pub enum Identifier {
    Variable(String),
    // attribute accessors - var1.field1 will be represented
    // as vec["var1", "field1"]
    AttrAccessor(Vec<String>),
}

/// Represents arithmetic binary operators
#[derive(Debug, Clone)]
pub enum Op {
    Add,
    Subtract,
    Multiply,
    Divide,
    Power
}

#[derive(Debug, Clone, PartialEq)]
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
#[derive(Debug, Clone)]
pub enum Expr {
    // Used to define enum matching for the custom message type
    MessageType(String),
    Identifier(Identifier),
    StorageRead(Key),
    Number(Number),
    String(String),
    Null,
    Type(Type),
    BinOp {
        lhs: Box<Expr>,
        op: Op,
        rhs: Box<Expr>,
    }
}

impl Expr {
    pub fn as_bytes(&self) -> Option<Vec<u8>> {
        match self {
            Expr::Number(n) => match n {
                Number::Int(i) => Some(i.to_le_bytes().to_vec()),
                Number::Float(f) => Some(f.to_le_bytes().to_vec()),
            },
            Expr::String(s) => unsafe { return Some(s.clone().as_mut_vec().to_vec()); },
            _ => None
        }
    }
}

/// Represents different Smart Contract entry points
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum EntryPoint {
    Instantiate,
    Execute,
    Query,
    Reply,
}

/// Represents all possible pre-defined input types, and also 
/// a Custom type for the SC's custom messages
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum InputType {
    DepsMut,
    Env,
    MessageInfo,
    Custom,
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
#[derive(Debug)]
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
#[derive(Debug)]
pub enum PathCondition {
    Bool(bool),
    RelBinOp {
        lhs: Box<Expr>,
        rel_op: RelOp,
        rhs: Box<Expr>,
    }
}

/// Represents a storage key. 
/// Can either be represented in Bytes if the SE-output is in base64,
/// or in the form of an expression otherwise to be computed at runtime.
#[derive(Debug, Clone)]
pub enum Key {
    Bytes(Vec<u8>),
    Expression {
        base: Vec<u8>,
        expr: Box<Expr>,
    }, 
}

/// Represents either a read or write to be stored as a RWS
#[derive(Debug)]
pub enum ReadWrite {
    Write {
        key: Key,
        value: Expr,
    },
    Read(Key),
}

pub type CondNodeRef = Rc<RefCell<Box<PathConditionNode>>>;
/// Represents a node in the path condition tree.
/// 
/// Each node has 1 condition and at least 1 positive and 1 negative branch.
/// 
/// If the node has information about the RWS, then it can have >1 child branches (positive/negative)
#[derive(Debug)]
pub enum PathConditionNode {
    /// Represents a full node associated to a condition, and both child branches.
    ConditionNode {
        /// Represents the boolean condition
        condition: Option<PathCondition>,
        
        // Rc for shared access to reference -> 
        // RefCell for mutating the inner data -> 
        // Box needed since it's recursive
        pos_branch: Option<CondNodeRef>,
        neg_branch: Option<CondNodeRef>,
    },
    // TODO - currently we only store gets that are not issued to the same position 
    // as the write (and that appear as a dependency for that write)
    /// Represents the RWS under a specific child branch (positive / negative)
    RWSNode(Vec<ReadWrite>),
    None,
}


pub type ArgTypes = HashMap<String, InputType>;
pub type CustomArgTypes = HashMap<String, HashMap<String, Type>>;

/// Represents all info related to each entry point:
/// 
/// Inputs, type_defs, and Path conditions (RWS)
#[derive(Debug)]
pub struct EntryPointProfile {
    /// Maps all input variable names to their types.
    pub inputs: ArgTypes,
    
    /// Stores type_defs for each atribute within each custom message type:
    /// ```
    /// struct AddUSer {
    /// 
    ///     field1: string,
    ///     field2: string 
    /// 
    /// }
    /// ```
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