use std::iter::Peekable;

use crate::tokens::{Token, TokenError, Tokens};

const BINARY_OPERATORS: [(Associativity, &[Token]); 3] = [
    (Associativity::Left, &[Token::Plus]),
    (Associativity::Left, &[Token::Asterisk]),
    (Associativity::Right, &[Token::Caret]),
];

pub struct Parser<'tokens> {
    tokens: Peekable<Tokens<'tokens>>,
}

impl<'tokens> Parser<'tokens> {
    pub fn new(tokens: Tokens<'tokens>) -> Self {
        Self {
            tokens: tokens.peekable(),
        }
    }

    fn expect(&mut self, expected: Token) -> ParseResult<()> {
        match self.tokens.next() {
            Some(token_result) => {
                let (token, start, end) = token_result
                    .map_err(|(error, start, end)| (ParseError::TokenError(error), start, end))?;

                if token == expected {
                    Ok(((), start, end))
                } else {
                    Err((ParseError::UnexpectedToken(token), start, end))
                }
            }
            None => Err((ParseError::UnexpectedEOF, 0, 0)),
        }
    }

    fn primary(&mut self) -> ParseResult<Expression> {
        let Some(token_result) = self.tokens.next() else {
            return Err((ParseError::UnexpectedEOF, 0, 0));
        };

        let (token, start, end) = token_result
            .map_err(|(error, start, end)| (ParseError::TokenError(error), start, end))?;

        match token {
            Token::NaturalNumber(nat) => Ok((Expression::NaturalNumber(nat), start, end)),
            Token::OpeningParenthesis => {
                let (expr, _, _) = self.expression()?;
                let ((), _, end) = self.expect(Token::ClosingParenthesis)?;
                Ok((expr, start, end))
            }
            unexpected => Err((ParseError::UnexpectedToken(unexpected), start, end)),
        }
    }

    fn binary(&mut self, precedence: usize) -> ParseResult<Expression> {
        if precedence >= BINARY_OPERATORS.len() {
            return self.primary();
        }

        let mut result = self.binary(precedence + 1)?;

        let (assoc, ops) = &BINARY_OPERATORS[precedence];
        match assoc {
            Associativity::Right => {
                if let Some(token_result) = self.tokens.peek() {
                    let (token, _, _) = token_result.as_ref().map_err(|(error, start, end)| {
                        (ParseError::TokenError(error.clone()), *start, *end)
                    })?;

                    if ops.contains(token) {
                        let bop = token.into();
                        self.tokens.next();
                        let (rhs, _, end) = self.binary(precedence)?;
                        result.0 = Expression::Binary {
                            lhs: Box::new(result.0),
                            rhs: Box::new(rhs),
                            bop,
                        };
                        result.2 = end;
                    }
                }
            }
            Associativity::Left => {
                while let Some(token_result) = self.tokens.peek() {
                    let (token, _, _) = token_result.as_ref().map_err(|(error, start, end)| {
                        (ParseError::TokenError(error.clone()), *start, *end)
                    })?;

                    if ops.contains(token) {
                        let bop = token.into();
                        self.tokens.next();
                        let (rhs, _, end) = self.binary(precedence + 1)?;
                        result.0 = Expression::Binary {
                            lhs: Box::new(result.0),
                            rhs: Box::new(rhs),
                            bop,
                        };
                        result.2 = end;
                    } else {
                        break;
                    }
                }
            }
            Associativity::None => {
                if let Some(token_result) = self.tokens.peek() {
                    let (token, _, _) = token_result.as_ref().map_err(|(error, start, end)| {
                        (ParseError::TokenError(error.clone()), *start, *end)
                    })?;

                    if ops.contains(token) {
                        let bop = token.into();
                        self.tokens.next();
                        let (rhs, _, end) = self.binary(precedence + 1)?;
                        result.0 = Expression::Binary {
                            lhs: Box::new(result.0),
                            rhs: Box::new(rhs),
                            bop,
                        };
                        result.2 = end;
                    }
                }
            }
        }
        Ok(result)
    }

    fn expression(&mut self) -> ParseResult<Expression> {
        self.binary(0)
    }

    pub fn parse(&mut self) -> ParseResult<Expression> {
        let (expr, start, end) = self.expression()?;

        match self.tokens.next() {
            Some(token_result) => {
                let (_, start, _) = token_result
                    .map_err(|(error, start, end)| (ParseError::TokenError(error), start, end))?;
                Err((ParseError::Unconsumed, start, 0))
            }
            None => Ok((expr, start, end)),
        }
    }
}

#[derive(Debug)]
pub enum ParseError {
    UnexpectedEOF,
    TokenError(TokenError),
    UnexpectedToken(Token),
    Unconsumed,
}

type ParseResult<T> = Result<(T, usize, usize), (ParseError, usize, usize)>;

#[derive(Debug)]
pub enum Expression {
    NaturalNumber(String),
    Binary {
        lhs: Box<Expression>,
        rhs: Box<Expression>,
        bop: BinaryOp,
    },
}

#[derive(Debug)]
pub enum BinaryOp {
    Addition,
    Multiplication,
    Exponentiation,
}

impl From<&Token> for BinaryOp {
    fn from(val: &Token) -> Self {
        match val {
            Token::Asterisk => Self::Multiplication,
            Token::Caret => Self::Exponentiation,
            Token::Plus => Self::Addition,
            _ => unreachable!(),
        }
    }
}

enum Associativity {
    Right,
    Left,
    None,
}
