use std::boxed::Box;

use super::token::Token;

// Expression Structure Nodes
#[derive(Debug, Clone)]
pub enum NodeTerm {
    IntLit(u32),
    Ident(String),
    Bool(bool),
    Paren(Box<NodeExpr>),
}

impl NodeTerm {
    pub fn operate(&self, op: &BinOp, other: &NodeTerm) -> Result<Option<NodeTerm>, String> {
        match self {
            NodeTerm::IntLit(num_1) => match other {
                NodeTerm::IntLit(num_2) => match op {
                    BinOp::Add => Ok(Some(NodeTerm::IntLit(num_1 + num_2))),
                    BinOp::Sub => Ok(Some(NodeTerm::IntLit(num_1 - num_2))),
                    BinOp::Mul => Ok(Some(NodeTerm::IntLit(num_1 * num_2))),
                    BinOp::Div => Ok(Some(NodeTerm::IntLit(num_1 / num_2))),
                    BinOp::Eq => Ok(Some(NodeTerm::Bool(num_1 == num_2))),
                    BinOp::Ne => Ok(Some(NodeTerm::Bool(num_1 != num_2))),
                    BinOp::Gt => Ok(Some(NodeTerm::Bool(num_1 > num_2))),
                    BinOp::Lt => Ok(Some(NodeTerm::Bool(num_1 < num_2))),
                    _ => Err(format!(
                        "invalid binary operation: {} {} {}",
                        num_1, op, num_2,
                    )),
                },
                NodeTerm::Bool(bl) => Err(format!(
                    "invalid binary operation: {} {} {}",
                    num_1, op, bl,
                )),
                NodeTerm::Ident(_) => Ok(None),
                NodeTerm::Paren(_) => Ok(None),
            },
            NodeTerm::Bool(bl_1) => match other {
                NodeTerm::Bool(bl_2) => match op {
                    BinOp::Eq => Ok(Some(NodeTerm::Bool(bl_1 == bl_2))),
                    BinOp::Ne => Ok(Some(NodeTerm::Bool(bl_1 != bl_2))),
                    BinOp::And => Ok(Some(NodeTerm::Bool(*bl_1 && *bl_2))),
                    BinOp::Or => Ok(Some(NodeTerm::Bool(*bl_1 || *bl_2))),
                    _ => Err(format!(
                        "invalid binary operation: {} {} {}",
                        bl_1, op, bl_2,
                    )),
                },
                NodeTerm::IntLit(num) => Err(format!(
                    "invalid binary operation: {} {} {}",
                    bl_1, op, num,
                )),
                NodeTerm::Ident(_) => Ok(None),
                NodeTerm::Paren(_) => Ok(None),
            },
            NodeTerm::Ident(_) => Ok(None),
            NodeTerm::Paren(_) => Ok(None),
        }
    }
}

impl std::fmt::Display for NodeTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NodeTerm::IntLit(val) => write!(f, "{}", val),
            NodeTerm::Bool(val) => write!(f, "{}", val),
            NodeTerm::Ident(val) => write!(f, "{}", val),
            NodeTerm::Paren(expr) => write!(f, "({})", expr.as_ref()),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    // maths
    Add,
    Sub,
    Mul,
    Div,
    // logic
    Eq,
    Ne,
    Gt,
    Lt,
    And,
    Or,
}

impl BinOp {
    pub fn from_token(token: &Token) -> BinOp {
        match token {
            Token::Plus => BinOp::Add,
            Token::Minus => BinOp::Sub,
            Token::Star => BinOp::Mul,
            Token::FSlash => BinOp::Div,
            Token::Equality => BinOp::Eq,
            Token::NonEquality => BinOp::Ne,
            Token::GreaterThan => BinOp::Gt,
            Token::LessThan => BinOp::Lt,
            Token::And => BinOp::And,
            Token::Or => BinOp::Or,
            _ => panic!("tried to convert a non bin-op Token to a BinOp"),
        }
    }

    pub fn get_instruction(&self) -> Result<&str, String> {
        match self {
            BinOp::Add => Ok("add"),
            BinOp::Sub => Ok("sub"),
            BinOp::Mul => Ok("mul"),
            BinOp::Div => Ok("udiv"),
            BinOp::And => Ok("and"),
            BinOp::Or => Ok("orr"),
            _ => Err(format!("binary operator doens't have instruction: {}", self)),
        }
    }

    pub fn get_flag(&self) -> Result<&str, String> {
        match self {
            BinOp::Eq => Ok("eq"),
            BinOp::Ne => Ok("ne"),
            BinOp::Gt => Ok("gt"),
            BinOp::Lt => Ok("lt"),
            _ => Err(format!("binary operator doens't have flag: {}", self)),
        }
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Gt => ">",
            BinOp::Lt => "<",
            BinOp::And => "&&",
            BinOp::Or => "||",
        })
    }
}

#[derive(Debug, Clone)]
pub struct NodeBinOp {
    pub lhs: Box<NodeExpr>,
    pub rhs: Box<NodeExpr>,
    pub op: BinOp,
}

impl std::fmt::Display for NodeBinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] {} [{}]", self.lhs, self.op, self.rhs)
    }
}

#[derive(Debug, Clone)]
pub enum NodeExpr {
    Term(NodeTerm),
    BinOp(NodeBinOp),
}

impl NodeExpr {
    // construct a binary operator expression, simplifying where possible
    pub fn new_bin_op_expr(
        lhs: Box<NodeExpr>,
        rhs: Box<NodeExpr>,
        op: BinOp,
    ) -> Result<NodeExpr, String> {
        // if either value isn't known at parsing - return BinOp
        let NodeExpr::Term(lhs_term) = lhs.as_ref() else {
            return Ok(NodeExpr::BinOp(NodeBinOp { lhs, rhs, op }));
        };
        let NodeExpr::Term(rhs_term) = rhs.as_ref() else {
            return Ok(NodeExpr::BinOp(NodeBinOp { lhs, rhs, op }));
        };
        // try to simplify the BinOp
        let new_term = lhs_term.operate(&op, rhs_term)?;
        match new_term {
            Some(new_term) => Ok(NodeExpr::Term(new_term)),
            None => Ok(NodeExpr::BinOp(NodeBinOp { lhs, rhs, op })),
        }
    }

    pub fn new_int(num: u32) -> NodeExpr {
        NodeExpr::Term(NodeTerm::IntLit(num))
    }
}

impl std::fmt::Display for NodeExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NodeExpr::Term(term) => term.fmt(f),
            NodeExpr::BinOp(bin_op) => bin_op.fmt(f),
        }
    }
}

// Statement Structure Nodes
#[derive(Debug)]
pub struct NodeExit {
    pub expr: NodeExpr,
}

#[derive(Debug)]
pub struct NodeLet {
    pub ident: String,
    pub expr: NodeExpr,
}

#[derive(Debug)]
pub struct NodeAssign {
    pub ident: String,
    pub expr: NodeExpr,
}

#[derive(Debug)]
pub struct NodeScope {
    pub stmts: Vec<NodeStmt>,
}

#[derive(Debug)]
pub struct NodeCondition {
    pub expr: NodeExpr,
    pub scope: NodeScope,
    pub else_scope: Option<NodeScope>,
}

#[derive(Debug)]
pub struct NodeLoop {
    pub scope: NodeScope,
}

// Program Structure Nodes
#[derive(Debug)]
pub enum NodeStmt {
    Exit(NodeExit),
    Let(NodeLet),
    Assign(NodeAssign),
    Scope(NodeScope),
    Condition(NodeCondition),
    Loop(NodeLoop),
    Continue,
    Break,
}

#[derive(Debug, Default)]
pub struct NodeProg {
    pub stmts: Vec<NodeStmt>,
}
