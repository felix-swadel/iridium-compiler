use super::cpu::Type;
use super::node::*;
use super::token::*;

pub struct Parser<'a> {
    tokens: &'a Vec<Token>,
    idx: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.idx)
    }

    fn get(&self) -> Result<&Token, String> {
        self.peek().ok_or("expected token, found EOF".to_owned())
    }

    fn advance(&mut self) {
        self.idx += 1;
    }

    fn done(&self) -> bool {
        self.idx >= self.tokens.len()
    }

    fn expect(&self, expected: TokenId) -> Result<Token, String> {
        match self.peek() {
            Some(actual) => {
                if actual.id() != expected {
                    Err(format!("expected {}, found {}", expected, actual))
                } else {
                    Ok(actual.clone())
                }
            }
            None => Err(format!("expected {}, found EOF", expected)),
        }
    }

    fn try_consume(&mut self, expected: TokenId) -> Result<Token, String> {
        let token = self.expect(expected)?;
        self.advance();
        Ok(token)
    }

    fn try_consume_type_name(&mut self) -> Result<Type, String> {
        let token = match self.peek() {
            Some(token) => match token {
                Token::Int32Name => Type::Int32,
                Token::BoolName => Type::Bool,
                _ => return Err(format!("expected type name, found {}", token)),
            },
            None => return Err("expected type name, found EOF".to_owned()),
        };
        self.advance();
        Ok(token)
    }
}

impl<'a> Parser<'a> {
    fn parse_term(&mut self) -> Result<NodeTerm, String> {
        let mut token = self.get()?.to_owned();
        let unary_op = match token {
            Token::Minus => {
                self.advance();
                token = self.get()?.to_owned();
                Some(UnaryOp::Neg)
            }
            Token::Bang => {
                self.advance();
                token = self.get()?.to_owned();
                Some(UnaryOp::Not)
            }
            _ => None,
        };
        match token {
            Token::Int32(int_lit) => {
                self.advance();
                match unary_op {
                    Some(op) => match op {
                        UnaryOp::Neg => Ok(NodeTerm::Int32(-int_lit)),
                        UnaryOp::Not => Err(format!("invalid unary operation: !{}", int_lit)),
                    },
                    None => Ok(NodeTerm::Int32(int_lit)),
                }
            }
            Token::Bool(bl_lit) => {
                self.advance();
                match unary_op {
                    Some(op) => match op {
                        UnaryOp::Not => Ok(NodeTerm::Bool(!bl_lit)),
                        UnaryOp::Neg => Err(format!("invalid unary operation: -{}", bl_lit)),
                    },
                    None => Ok(NodeTerm::Bool(bl_lit)),
                }
            }
            Token::Ident(ident) => {
                self.advance();
                match unary_op {
                    Some(op) => Ok(NodeTerm::UnaryOp(NodeUnaryOp {
                        op,
                        term: Box::new(NodeTerm::Ident(ident)),
                    })),
                    None => Ok(NodeTerm::Ident(ident)),
                }
            }
            Token::OpenParen => {
                self.advance();
                let expr = self.parse_expr(0)?;
                self.try_consume(TokenId::CloseParen)?;
                // simplify the parens to a basic term if possible
                let term = match expr {
                    NodeExpr::Term(term) => term,
                    NodeExpr::BinOp(_) => NodeTerm::Paren(Box::new(expr)),
                };
                match unary_op {
                    Some(op) => Ok(NodeTerm::UnaryOp(NodeUnaryOp {
                        op,
                        term: Box::new(term),
                    })),
                    None => Ok(term),
                }
            }
            _ => Err(format!("expected term, found: {:?}", token)),
        }
    }

    fn parse_expr(&mut self, min_prec: usize) -> Result<NodeExpr, String> {
        let term = self.parse_term()?;
        let mut lhs = NodeExpr::Term(term);

        // precedence climbing
        loop {
            // extract next token
            let Some(token) = self.peek() else {
                break;
            };
            // check that it's a binary operator
            let Some(prec) = token.has_prec() else {
                break;
            };
            // check that it has high enough precedence
            if prec < min_prec {
                break;
            }
            let op = BinOp::from_token(token);
            // we have a valid BinOp expression to parse
            self.advance();
            let next_min_prec = prec + 1;
            let rhs = self.parse_expr(next_min_prec)?;
            // construct BinOp and store it in lhs
            lhs = NodeExpr::new_bin_op_expr(Box::new(lhs), Box::new(rhs), op)?;
        }

        Ok(lhs)
    }

    // exit(<expr>);
    fn parse_exit(&mut self) -> Result<NodeExit, String> {
        // extract `exit`
        self.try_consume(TokenId::Exit)?;
        // extract (
        self.try_consume(TokenId::OpenParen)?;
        // extract expression
        let expr = match self.parse_expr(0) {
            Ok(expr) => expr,
            Err(e) => return Err(e),
        };
        // extract )
        self.try_consume(TokenId::CloseParen)?;
        // extract ;
        self.try_consume(TokenId::Semi)?;
        Ok(NodeExit { expr })
    }

    // let <ident> = <expr>;
    fn parse_let(&mut self) -> Result<NodeLet, String> {
        // extract `let`
        self.try_consume(TokenId::Let)?;
        // extract identifier
        let Token::Ident(ident) = self.try_consume(TokenId::Ident)? else {
            unreachable!()
        };
        // check for explicit type
        let Some(next) = self.peek() else {
            return Err("expected `=` or `:`, found EOF".to_owned());
        };
        let exp_type = match next {
            Token::Equals => None,
            Token::Colon => {
                self.advance();
                Some(self.try_consume_type_name()?)
            }
            _ => return Err(format!("expected `=` or `:`, found {}", next)),
        };
        // extract =
        self.try_consume(TokenId::Equals)?;
        // extract expression
        let expr = self.parse_expr(0)?;
        // extract ;
        self.try_consume(TokenId::Semi)?;
        Ok(NodeLet {
            ident: ident.clone(),
            exp_type,
            expr,
        })
    }

    // <ident> = <expr>;
    fn parse_assign(&mut self) -> Result<NodeAssign, String> {
        // extract identifier
        let Token::Ident(ident) = self.try_consume(TokenId::Ident)? else {
            unreachable!()
        };
        // extract =
        self.try_consume(TokenId::Equals)?;
        // extract expression
        let expr = self.parse_expr(0)?;
        // extract ;
        self.try_consume(TokenId::Semi)?;
        Ok(NodeAssign {
            ident: ident.clone(),
            expr,
        })
    }

    // { <stmt>* }
    fn parse_scope(&mut self) -> Result<NodeScope, String> {
        // extract `{`
        self.try_consume(TokenId::OpenCurly)?;
        let mut stmts = Vec::new();
        while let Some(token) = self.peek() {
            if token.id() == TokenId::CloseCurly {
                break;
            }
            let node_stmt = self.parse_stmt()?;
            stmts.push(node_stmt);
        }
        // extract `}`
        self.try_consume(TokenId::CloseCurly)?;
        Ok(NodeScope { stmts })
    }

    // if <expr> <scope>
    fn parse_condition(&mut self) -> Result<NodeCondition, String> {
        // extract `if`
        self.try_consume(TokenId::If)?;
        let expr = self.parse_expr(0)?;
        // check that term can be bool
        if let NodeExpr::Term(NodeTerm::Int32(_)) = expr {
            return Err(format!("invalid conditional expression: {}", expr,));
        }
        let scope = self.parse_scope()?;
        if let Some(Token::Else) = self.peek() {
            // iterate over `else`
            self.advance();
            let else_scope = self.parse_scope()?;
            Ok(NodeCondition {
                expr,
                scope,
                else_scope: Some(else_scope),
            })
        } else {
            Ok(NodeCondition {
                expr,
                scope,
                else_scope: None,
            })
        }
    }

    fn parse_loop(&mut self) -> Result<NodeLoop, String> {
        // extract `loop`
        self.try_consume(TokenId::Loop)?;
        let scope = self.parse_scope()?;
        Ok(NodeLoop { scope })
    }

    fn parse_while(&mut self) -> Result<NodeWhile, String> {
        // extract `while`
        self.try_consume(TokenId::While)?;
        let expr = self.parse_expr(0)?;
        let scope = self.parse_scope()?;
        Ok(NodeWhile { expr, scope })
    }

    fn parse_continue(&mut self) -> Result<NodeStmt, String> {
        // consume `continue`
        self.try_consume(TokenId::Continue)?;
        // consume `'`
        self.try_consume(TokenId::Semi)?;
        Ok(NodeStmt::Continue)
    }

    fn parse_break(&mut self) -> Result<NodeStmt, String> {
        // consume `break`
        self.try_consume(TokenId::Break)?;
        // consume `'`
        self.try_consume(TokenId::Semi)?;
        Ok(NodeStmt::Break)
    }

    fn parse_stmt(&mut self) -> Result<NodeStmt, String> {
        // extract next token
        let token = match self.peek() {
            Some(token) => token,
            None => return Err(String::from("ran out of tokens while parsing statment")),
        };
        // parse statement based on token
        match token.id() {
            // statements with explicit start tokens
            TokenId::Exit => Ok(NodeStmt::Exit(self.parse_exit()?)),
            TokenId::Let => Ok(NodeStmt::Let(self.parse_let()?)),
            TokenId::OpenCurly => Ok(NodeStmt::Scope(self.parse_scope()?)),
            TokenId::If => Ok(NodeStmt::Condition(self.parse_condition()?)),
            TokenId::Loop => Ok(NodeStmt::Loop(self.parse_loop()?)),
            TokenId::While => Ok(NodeStmt::While(self.parse_while()?)),
            TokenId::Continue => Ok(self.parse_continue()?),
            TokenId::Break => Ok(self.parse_break()?),
            // statements with syntactic structure
            TokenId::Ident => Ok(NodeStmt::Assign(self.parse_assign()?)),
            _ => Err(format!("expected statement, found: {:?}", token)),
        }
    }
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a Vec<Token>) -> Parser {
        Parser { tokens, idx: 0 }
    }

    pub fn parse(&mut self) -> Result<NodeProg, String> {
        let mut prog = NodeProg::default();
        while !self.done() {
            // try to parse a statement
            match self.parse_stmt() {
                Ok(stmt) => prog.stmts.push(stmt),
                Err(e) => return Err(e),
            }
        }
        Ok(prog)
    }
}
