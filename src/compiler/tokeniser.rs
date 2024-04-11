use phf::{phf_map, Map};
use std::mem;

use super::token::Token;

const KEYWORDS: Map<&'static str, Token> = phf_map! {
    "exit" => Token::Exit,
    "let" => Token::Let,
    "if" => Token::If,
    "else" => Token::Else,
    "loop" => Token::Loop,
    "while" => Token::While,
    "continue" => Token::Continue,
    "break" => Token::Break,
    "true" => Token::Bool(true),
    "false" => Token::Bool(false),
};

#[derive(Debug, PartialEq)]
enum BufType {
    Unset,
    Word,
    Number,
}

struct TokenBuf {
    buf: String,
    buf_type: BufType,
}

impl TokenBuf {
    pub fn new() -> TokenBuf {
        TokenBuf {
            buf: String::new(),
            buf_type: BufType::Unset,
        }
    }

    pub fn push(&mut self, c: char) -> Result<(), String> {
        match self.buf_type {
            BufType::Unset => {
                // this is the first character - check for buffer type
                if c.is_ascii_digit() {
                    self.buf_type = BufType::Number;
                } else if c.is_ascii_alphabetic() {
                    self.buf_type = BufType::Word;
                } else {
                    return Err(format!("Unexpected character: {}", c));
                }
            }
            BufType::Number => {
                // check for digit
                if !c.is_ascii_digit() {
                    return Err(format!("Invalid char in number: {}", c));
                }
            }
            BufType::Word => {
                // check for alphanumeric
                if !c.is_ascii_alphanumeric() {
                    return Err(format!("Invalid char in identifier: {}", c));
                }
            }
        }
        self.buf.push(c);
        Ok(())
    }

    pub fn is_empty(&self) -> bool {
        self.buf.is_empty()
    }

    // utility function to reset buffer and return string
    fn extract(&mut self) -> String {
        self.buf_type = BufType::Unset;
        mem::replace(&mut self.buf, String::new())
    }

    fn reset(&mut self) {
        self.buf.clear();
        self.buf_type = BufType::Unset;
    }

    pub fn extract_token(&mut self) -> Token {
        assert_ne!(self.buf_type, BufType::Unset);
        match self.buf_type {
            BufType::Number => {
                let num = match self.buf.parse() {
                    Ok(num) => num,
                    Err(_) => panic!("couldn't parse string to u32: {}", self.buf),
                };
                self.reset();
                Token::Int32(num)
            }
            BufType::Word => {
                if let Some(token) = KEYWORDS.get(&self.buf) {
                    // check if string is keyword
                    self.reset();
                    token.clone()
                } else {
                    // otherwise assume it's an identifier
                    Token::Ident(self.extract())
                }
            }
            BufType::Unset => unreachable!(),
        }
    }
}

pub fn tokenise(text: &String) -> Result<Vec<Token>, String> {
    let mut iter = text.chars().peekable();
    let mut tokens = Vec::new();
    let mut buf = TokenBuf::new();
    // iterate through characters of text
    while let Some(c) = iter.next() {
        // check for control characters
        if c.is_whitespace() {
            if !buf.is_empty() {
                tokens.push(buf.extract_token());
            }
            continue;
        }
        // check for comment
        if c == '/' {
            // defined by two slashes
            if let Some(&'/') = iter.peek() {
                iter.next().unwrap(); 
                // we've found a comment
                if !buf.is_empty() {
                    tokens.push(buf.extract_token());
                }
                // iterate until next newline
                while let Some(c) = iter.next() {
                    if c == '\n' {
                        break;
                    }
                }
                continue;
            }
        }
        let token = match c {
            // maths symbols
            '+' => Some(Token::Plus),
            '-' => Some(Token::Minus),
            '*' => Some(Token::Star),
            '/' => Some(Token::FSlash),
            // logical operators
            '>' => Some(Token::GreaterThan),
            '<' => Some(Token::LessThan),
            // control characters
            ';' => Some(Token::Semi),
            '(' => Some(Token::OpenParen),
            ')' => Some(Token::CloseParen),
            '{' => Some(Token::OpenCurly),
            '}' => Some(Token::CloseCurly),
            // operators with multiple characters
            '=' => {
                if let Some(next_c) = iter.peek() {
                    if *next_c == '=' {
                        iter.next();
                        Some(Token::Equality)
                    } else {
                        Some(Token::Equals)
                    }
                } else {
                    Some(Token::Equals)
                }
            }
            '!' => {
                if let Some(next_c) = iter.peek() {
                    if *next_c == '=' {
                        iter.next();
                        Some(Token::NonEquality)
                    } else {
                        return Err("unexpected token: `!`".to_owned());
                    }
                } else {
                    return Err("unexpected token: `!`".to_owned());
                }
            }
            '&' => {
                if let Some(next_c) = iter.peek() {
                    if *next_c == '&' {
                        iter.next();
                        Some(Token::And)
                    } else {
                        return Err("unexpected token: `&`".to_owned());
                    }
                } else {
                    return Err("unexpected token: `&`".to_owned());
                }
            }
            '|' => {
                if let Some(next_c) = iter.peek() {
                    if *next_c == '|' {
                        iter.next();
                        Some(Token::Or)
                    } else {
                        return Err("unexpected token: `|`".to_owned());
                    }
                } else {
                    return Err("unexpected token: `|`".to_owned());
                }
            }
            _ => None,
        };
        match token {
            Some(token) => {
                if !buf.is_empty() {
                    tokens.push(buf.extract_token());
                }
                tokens.push(token);
            }
            None => {
                buf.push(c)?;
            }
        }
    }
    Ok(tokens)
}
