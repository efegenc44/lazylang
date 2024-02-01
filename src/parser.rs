use std::iter::Peekable;

use crate::{ranged::Ranged, tokens::{Token, TokenError, Tokens}};

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
                let (token, start, end) = token_result?.as_tuple();

                if token == expected {
                    Ok(Ranged::new((), start, end))
                } else {
                    Err(Ranged::new(ParseError::UnexpectedToken(token), start, end))
                }
            }
            None => Err(Ranged::new(ParseError::UnexpectedEOF, 0, 0)),
        }
    }

    fn primary(&mut self) -> ParseResult<Expression> {
        let Some(token_result) = self.tokens.next() else {
            return Err(Ranged::new(ParseError::UnexpectedEOF, 0, 0));
        };

        let (token, start, end) = token_result?.as_tuple();

        match token {
            Token::NaturalNumber(nat) => Ok(Ranged::new(Expression::NaturalNumber(nat), start, end)),
            Token::OpeningParenthesis => {
                let (expr, _, _) = self.expression()?.as_tuple();
                let ((), _, end) = self.expect(Token::ClosingParenthesis)?.as_tuple();
                Ok(Ranged::new(expr, start, end))
            }
            unexpected => Err(Ranged::new(ParseError::UnexpectedToken(unexpected), start, end)),
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
                    let (token, _, _) = token_result.as_ref()?.as_ref_tuple();

                    if ops.contains(token) {
                        let bop = token.into();
                        self.tokens.next();
                        let (rhs, _, end) = self.binary(precedence)?.as_tuple();
                        result.data = Expression::Binary {
                            lhs: Box::new(result.data),
                            rhs: Box::new(rhs),
                            bop,
                        };
                        result.end = end;
                    }
                }
            }
            Associativity::Left => {
                while let Some(token_result) = self.tokens.peek() {
                    let (token, _, _) = token_result.as_ref()?.as_ref_tuple();

                    if ops.contains(token) {
                        let bop = token.into();
                        self.tokens.next();
                        let (rhs, _, end) = self.binary(precedence + 1)?.as_tuple();
                        result.data = Expression::Binary {
                            lhs: Box::new(result.data),
                            rhs: Box::new(rhs),
                            bop,
                        };
                        result.end = end;
                    } else {
                        break;
                    }
                }
            }
            Associativity::None => {
                if let Some(token_result) = self.tokens.peek() {
                    let (token, _, _) = token_result.as_ref()?.as_ref_tuple();

                    if ops.contains(token) {
                        let bop = token.into();
                        self.tokens.next();
                        let (rhs, _, end) = self.binary(precedence + 1)?.as_tuple();
                        result.data = Expression::Binary {
                            lhs: Box::new(result.data),
                            rhs: Box::new(rhs),
                            bop,
                        };
                        result.end = end;
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
        let (expr, start, end) = self.expression()?.as_tuple();

        match self.tokens.next() {
            Some(token_result) => {
                let (_, start, _) = token_result?.as_tuple();
                Err(Ranged::new(ParseError::Unconsumed, start, 0))
            }
            None => Ok(Ranged::new(expr, start, end)),
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

impl From<Ranged<TokenError>> for Ranged<ParseError> {
    fn from(value: Ranged<TokenError>) -> Self {
        let (data, start, end) = value.as_tuple();
        Self::new(ParseError::TokenError(data), start, end)
    }
}

impl From<&Ranged<TokenError>> for Ranged<ParseError> {
    fn from(value: &Ranged<TokenError>) -> Self {
        let (data, start, end) = value.as_ref_tuple();
        Self::new(ParseError::TokenError(data.clone()), *start, *end)
    }
}

type ParseResult<T> = Result<Ranged<T>, Ranged<ParseError>>;

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
