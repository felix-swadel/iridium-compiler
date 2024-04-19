use std::fmt;

#[derive(Debug, Clone)]
pub enum Token {
    // keywords
    Exit,
    Let,
    If,
    Else,
    Loop,
    While,
    Continue,
    Break,
    // values
    Ident(String),
    Int32(i32),
    Bool(bool),
    // type names
    Int32Name,
    BoolName,
    // maths symbols
    Plus,
    Minus,
    Star,
    FSlash,
    // logical operators
    Bang,
    Equality,
    NonEquality,
    GreaterThan,
    LessThan,
    And,
    Or,
    // control characters
    Semi,
    Colon,
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
            Token::While => TokenId::While,
            Token::Ident(_) => TokenId::Ident,
            Token::Int32(_) => TokenId::Int32,
            Token::Bool(_) => TokenId::Bool,
            Token::Int32Name => TokenId::Int32Name,
            Token::BoolName => TokenId::BoolName,
            Token::Plus => TokenId::Plus,
            Token::Minus => TokenId::Minus,
            Token::Star => TokenId::Star,
            Token::FSlash => TokenId::FSlash,
            Token::Bang => TokenId::Bang,
            Token::Equality => TokenId::Equality,
            Token::NonEquality => TokenId::NonEquality,
            Token::GreaterThan => TokenId::GreaterThan,
            Token::LessThan => TokenId::LessThan,
            Token::And => TokenId::And,
            Token::Or => TokenId::Or,
            Token::Semi => TokenId::Semi,
            Token::Colon => TokenId::Colon,
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
            Token::Equality | Token::NonEquality | Token::GreaterThan | Token::LessThan => Some(2),
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
    While,
    // values
    Ident,
    Int32,
    Bool,
    // type names
    Int32Name,
    BoolName,
    // maths symbols
    Plus,
    Minus,
    Star,
    FSlash,
    // logical operators
    Bang,
    Equality,
    NonEquality,
    GreaterThan,
    LessThan,
    And,
    Or,
    // control characters
    Semi,
    Colon,
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
                TokenId::While => "`while`",
                TokenId::Continue => "`continue`",
                TokenId::Break => "`break`",
                TokenId::Ident => "<identifier>",
                TokenId::Int32 => "<integer-literal>",
                TokenId::Bool => "<bool>",
                TokenId::Int32Name => "`i32`",
                TokenId::BoolName => "`bool`",
                TokenId::Plus => "`+`",
                TokenId::Minus => "`-`",
                TokenId::Star => "`*`",
                TokenId::FSlash => "`/`",
                TokenId::Bang => "`!`",
                TokenId::Equality => "`==`",
                TokenId::NonEquality => "`!=`",
                TokenId::GreaterThan => "`>`",
                TokenId::LessThan => "`<`",
                TokenId::And => "`&&`",
                TokenId::Or => "`||`",
                TokenId::Semi => "`;`",
                TokenId::Colon => "`:`",
                TokenId::OpenParen => "`(`",
                TokenId::CloseParen => "`)`",
                TokenId::OpenCurly => "`{`",
                TokenId::CloseCurly => "`}`",
                TokenId::Equals => "`=`",
            }
        )
    }
}
