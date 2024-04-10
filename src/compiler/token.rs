use std::fmt;

#[derive(Debug, Clone)]
pub enum Token {
    // keywords
    Exit,
    Let,
    If,
    Else,
    Loop,
    Continue,
    Break,
    // values
    Ident(String),
    Int32(u32),
    Bool(bool),
    // maths symbols
    Plus,
    Minus,
    Star,
    FSlash,
    // logical operators
    Equality,
    NonEquality,
    GreaterThan,
    LessThan,
    And,
    Or,
    // control characters
    Semi,
    OpenParen,
    CloseParen,
    OpenCurly,
    CloseCurly,
    Equals,
}

impl Token {
    pub fn id(&self) -> TokenId {
        match self {
            Token::Exit => TokenId::Exit,
            Token::Let => TokenId::Let,
            Token::If => TokenId::If,
            Token::Else => TokenId::Else,
            Token::Loop => TokenId::Loop,
            Token::Continue => TokenId::Continue,
            Token::Break => TokenId::Break,
            Token::Ident(_) => TokenId::Ident,
            Token::Int32(_) => TokenId::Int32,
            Token::Bool(_) => TokenId::Bool,
            Token::Plus => TokenId::Plus,
            Token::Minus => TokenId::Minus,
            Token::Star => TokenId::Star,
            Token::FSlash => TokenId::FSlash,
            Token::Equality => TokenId::Equality,
            Token::NonEquality => TokenId::NonEquality,
            Token::GreaterThan => TokenId::GreaterThan,
            Token::LessThan => TokenId::LessThan,
            Token::And => TokenId::And,
            Token::Or => TokenId::Or,
            Token::Semi => TokenId::Semi,
            Token::OpenParen => TokenId::OpenParen,
            Token::CloseParen => TokenId::CloseParen,
            Token::OpenCurly => TokenId::OpenCurly,
            Token::CloseCurly => TokenId::CloseCurly,
            Token::Equals => TokenId::Equals,
        }
    }

    pub fn has_prec(&self) -> Option<usize> {
        match self {
            Token::Or => Some(0),
            Token::And => Some(1),
            Token::Equality | Token::NonEquality |
            Token::GreaterThan | Token::LessThan => Some(2),
            Token::Plus | Token::Minus => Some(3),
            Token::Star | Token::FSlash => Some(4),
            _ => None,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Ident(s) => write!(f, "identifier: {}", s),
            Token::Int32(n) => write!(f, "integer-literal: {}", n),
            Token::Bool(b) => write!(f, "bool: {}", b),
            _ => self.id().fmt(f),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum TokenId {
    // keywords
    Exit,
    Let,
    If,
    Else,
    Loop,
    Continue,
    Break,
    // values
    Ident,
    Int32,
    Bool,
    // maths symbols
    Plus,
    Minus,
    Star,
    FSlash,
    // logical operators
    Equality,
    NonEquality,
    GreaterThan,
    LessThan,
    And,
    Or,
    // control characters
    Semi,
    OpenParen,
    CloseParen,
    OpenCurly,
    CloseCurly,
    Equals,
}

impl fmt::Display for TokenId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TokenId::Exit => "`exit`",
                TokenId::Let => "`let`",
                TokenId::If => "`if`",
                TokenId::Else => "`else`",
                TokenId::Loop => "`loop`",
                TokenId::Continue => "`continue`",
                TokenId::Break => "`break`",
                TokenId::Ident => "<identifier>",
                TokenId::Int32 => "<integer-literal>",
                TokenId::Bool => "<bool>",
                TokenId::Plus => "`+`",
                TokenId::Minus => "`-`",
                TokenId::Star => "`*`",
                TokenId::FSlash => "`/`",
                TokenId::Equality => "`==`",
                TokenId::NonEquality => "`!=`",
                TokenId::GreaterThan => "`>`",
                TokenId::LessThan => "`<`",
                TokenId::And => "`&&`",
                TokenId::Or => "`||`",
                TokenId::Semi => "`;`",
                TokenId::OpenParen => "`(`",
                TokenId::CloseParen => "`)`",
                TokenId::OpenCurly => "`{`",
                TokenId::CloseCurly => "`}`",
                TokenId::Equals => "`=`",
            }
        )
    }
}
