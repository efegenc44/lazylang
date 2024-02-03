use core::fmt;
use std::{io, iter::Peekable};

use crate::{
    error,
    ranged::Ranged,
    tokens::{Token, TokenError, Tokens},
};

const BINARY_OPERATORS: [(Token, Associativity, usize); 3] = [
    (Token::Colon, Associativity::Right, 0),
    (Token::Plus, Associativity::Left, 1),
    (Token::Asterisk, Associativity::Left, 2),
];

pub struct Parser<'source> {
    tokens: Peekable<Tokens<'source>>,
}

impl<'source> Parser<'source> {
    pub fn new(tokens: Tokens<'source>) -> Self {
        Self {
            tokens: tokens.peekable(),
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    fn expect(&mut self, expected: Token) -> ParseResult<()> {
        match self.tokens.next() {
            Some(token_result) => {
                let (token, ranges) = token_result?.into_tuple();

                if token == expected {
                    Ok(Ranged::new((), ranges))
                } else {
                    Err(Ranged::new(ParseError::UnexpectedToken(token), ranges))
                }
            }
            None => Err(Ranged::new(ParseError::UnexpectedEOF, Default::default())),
        }
    }

    fn expect_ident(&mut self) -> ParseResult<String> {
        match self.tokens.next() {
            Some(token_result) => {
                let (token, ranges) = token_result?.into_tuple();

                if let Token::Identifier(name) = token {
                    Ok(Ranged::new(name, ranges))
                } else {
                    Err(Ranged::new(ParseError::UnexpectedToken(token), ranges))
                }
            }
            None => Err(Ranged::new(ParseError::UnexpectedEOF, Default::default())),
        }
    }

    fn primary_pattern(&mut self) -> ParseResult<Pattern> {
        let Some(token_result) = self.tokens.next() else {
            return Err(Ranged::new(ParseError::UnexpectedEOF, Default::default()));
        };

        let (token, ranges) = token_result?.into_tuple();

        match token {
            Token::Identifier(ident) => Ok(Ranged::new(Pattern::All(ident), ranges)),
            Token::NaturalNumber(nat) => Ok(Ranged::new(Pattern::NaturalNumber(nat), ranges)),
            Token::OpeningParenthesis => {
                let pattern = self.pattern()?;
                let ends = self.expect(Token::ClosingParenthesis)?.ends();
                Ok(Ranged::new(pattern.data, (ranges.0, ends)))
            }
            unexpected => Err(Ranged::new(ParseError::UnexpectedToken(unexpected), ranges)),
        }
    }

    fn pair_pattern(&mut self) -> ParseResult<Pattern> {
        let primary = self.primary_pattern()?;

        if let Some(token_result) = self.tokens.peek() {
            let Token::Colon = token_result.as_ref()?.data else {
                return Ok(primary);
            };
            self.tokens.next();
            let second = self.pair_pattern()?;
            let starts = primary.starts();
            let ends = second.ends();
            return Ok(Ranged::new(
                Pattern::Pair {
                    first: Box::new(primary),
                    second: Box::new(second),
                },
                (starts, ends),
            ));
        }

        Ok(primary)
    }

    fn pattern(&mut self) -> ParseResult<Pattern> {
        self.pair_pattern()
    }

    fn parse_let(&mut self, starts: (usize, usize)) -> ParseResult<Expression> {
        let pattern = self.pattern()?;
        self.expect(Token::Equals)?;
        let value_expr = Box::new(self.expression()?);
        self.expect(Token::InKeyword)?;
        let return_expr = Box::new(self.expression()?);
        let ends = return_expr.ends();
        Ok(Ranged::new(
            Expression::Let {
                pattern,
                value_expr,
                return_expr,
            },
            (starts, ends),
        ))
    }

    fn parse_lambda(&mut self, starts: (usize, usize)) -> ParseResult<Expression> {
        self.expect(Token::OpeningParenthesis)?;
        let mut args = vec![];
        if let Some(token_result) = self.tokens.peek() {
            if !matches!(token_result.as_ref()?.data, Token::ClosingParenthesis) {
                args.push(self.pattern()?);
                while let Some(token_result) = self.tokens.peek() {
                    if token_result.as_ref()?.data == Token::ClosingParenthesis {
                        break;
                    };
                    self.expect(Token::Comma)?;
                    args.push(self.pattern()?);
                }
            }
        }
        self.expect(Token::ClosingParenthesis)?;
        let expr = Box::new(self.expression()?);
        let ends = expr.ends();

        Ok(Ranged::new(
            Expression::Function { args, expr },
            (starts, ends),
        ))
    }

    fn parse_import(&mut self, starts: (usize, usize)) -> ParseResult<Expression> {
        let part = self.expect_ident()?;
        let mut ends = part.ends();
        let mut parts = vec![part.data];
        while let Some(token_result) = self.tokens.peek() {
            let Token::Dot = token_result.as_ref()?.data else {
                break
            };
            self.tokens.next();
            let part = self.expect_ident()?;
            ends = part.ends();
            parts.push(part.data);
        }

        Ok(Ranged::new(Expression::Import(parts), (starts, ends)))
    }

    fn primary(&mut self) -> ParseResult<Expression> {
        let Some(token_result) = self.tokens.next() else {
            return Err(Ranged::new(ParseError::UnexpectedEOF, Default::default()));
        };

        let (token, ranges) = token_result?.into_tuple();

        match token {
            Token::Identifier(ident) => Ok(Ranged::new(Expression::Identifier(ident), ranges)),
            Token::NaturalNumber(nat) => Ok(Ranged::new(Expression::NaturalNumber(nat), ranges)),
            Token::OpeningParenthesis => {
                let expr = self.expression()?.data;
                let ends = self.expect(Token::ClosingParenthesis)?.ends();
                Ok(Ranged::new(expr, (ranges.0, ends)))
            }
            Token::LetKeyword => self.parse_let(ranges.0),
            Token::FunKeyword => self.parse_lambda(ranges.0),
            Token::ImportKeyword => self.parse_import(ranges.0),
            unexpected => Err(Ranged::new(ParseError::UnexpectedToken(unexpected), ranges)),
        }
    }

    fn application_and_access(&mut self) -> ParseResult<Expression> {
        let mut expr = self.primary()?;

        while let Some(token_result) = self.tokens.peek() {
            match &token_result.as_ref()?.data {
                Token::OpeningParenthesis => {
                    self.tokens.next();
                    let mut args = vec![];
                    if let Some(token_result) = self.tokens.peek() {
                        if !matches!(token_result.as_ref()?.data, Token::ClosingParenthesis) {
                            args.push(self.expression()?);
                            while let Some(token_result) = self.tokens.peek() {
                                if token_result.as_ref()?.data == Token::ClosingParenthesis {
                                    break;
                                };
                                self.expect(Token::Comma)?;
                                args.push(self.expression()?);
                            }
                        }
                    }
                    let starts = expr.starts();
                    let ends = self.expect(Token::ClosingParenthesis)?.ends();

                    expr = Ranged::new(
                        Expression::Application {
                            expr: Box::new(expr),
                            args,
                        },
                        (starts, ends),
                    );
                }
                Token::Dot => {
                    self.tokens.next();
                    let what = self.expect_ident()?;
                    let starts = expr.starts();
                    let ends = what.ends();
                    expr = Ranged::new(
                        Expression::Access {
                            from: Box::new(expr),
                            what,
                        },
                        (starts, ends),
                    );
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn binary(&mut self, min_prec: usize) -> ParseResult<Expression> {
        let mut expr = self.application_and_access()?;

        while let Some(token_result) = self.tokens.peek() {
            let token = &token_result.as_ref()?.data;

            let Some((op_token, assoc, prec)) = BINARY_OPERATORS.iter().find(|(op_token, _, _)| op_token == token) else {
                break;
            };

            if prec < &min_prec {
                break;
            }

            let bop = op_token.into();
            let prec = *prec;

            self.tokens.next();
            let rhs = self.binary(prec + usize::from(assoc != &Associativity::Right))?;

            let starts = expr.starts();
            let ends = rhs.ends();
            expr = Ranged::new(
                Expression::Binary {
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                    bop,
                },
                (starts, ends),
            );

            if assoc == &Associativity::None {
                break;
            }
        }

        Ok(expr)
    }

    fn expression(&mut self) -> ParseResult<Expression> {
        self.binary(0)
    }

    pub fn parse_expr(&mut self) -> ParseResult<Expression> {
        let (expr, ranges) = self.expression()?.into_tuple();

        match self.tokens.next() {
            Some(token_result) => {
                let starts = token_result?.starts();
                Err(Ranged::new(ParseError::Unconsumed, (starts, (0, 0))))
            }
            None => Ok(Ranged::new(expr, ranges)),
        }
    }

    pub fn parse_module(
        &mut self,
    ) -> Result<Vec<(String, Ranged<Expression>)>, Ranged<ParseError>> {
        let mut definitions = vec![];
        while self.tokens.peek().is_some() {
            let name = self.expect_ident()?.data;
            self.expect(Token::Equals)?;
            definitions.push((name, self.expression()?));
        }

        Ok(definitions)
    }
}

#[derive(Debug)]
pub enum ParseError {
    UnexpectedEOF,
    TokenError(TokenError),
    UnexpectedToken(Token),
    Unconsumed,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedEOF => write!(f, "Unexpectedly encountered EOF while parsing."),
            Self::TokenError(error) => write!(f, "{error}"),
            Self::UnexpectedToken(token) => write!(f, "`{token:?}` was not expected."),
            Self::Unconsumed => write!(f, "Some tokens couldn't be consumed."),
        }
    }
}

impl From<Ranged<TokenError>> for Ranged<ParseError> {
    fn from(value: Ranged<TokenError>) -> Self {
        let ranges = value.ranges();
        Self::new(ParseError::TokenError(value.data), ranges)
    }
}

impl From<&Ranged<TokenError>> for Ranged<ParseError> {
    fn from(value: &Ranged<TokenError>) -> Self {
        Self::new(ParseError::TokenError(value.data.clone()), value.ranges())
    }
}

impl Ranged<ParseError> {
    pub fn report(&self, source_name: &str) -> io::Result<()> {
        match self.data {
            ParseError::UnexpectedEOF => todo!(),
            ParseError::Unconsumed => todo!(),
            _ => (),
        }

        error::report(self, source_name, "parsing")
    }
}

type ParseResult<T> = Result<Ranged<T>, Ranged<ParseError>>;

#[derive(Clone, Debug)]
pub enum Expression {
    Identifier(String),
    NaturalNumber(String),
    Binary {
        lhs: Box<Ranged<Expression>>,
        rhs: Box<Ranged<Expression>>,
        bop: BinaryOp,
    },
    Let {
        pattern: Ranged<Pattern>,
        value_expr: Box<Ranged<Expression>>,
        return_expr: Box<Ranged<Expression>>,
    },
    Function {
        args: Vec<Ranged<Pattern>>,
        expr: Box<Ranged<Expression>>,
    },
    Application {
        expr: Box<Ranged<Expression>>,
        args: Vec<Ranged<Expression>>,
    },
    Access {
        from: Box<Ranged<Expression>>,
        what: Ranged<String>,
    },
    Import(Vec<String>),
}

#[derive(Clone, Debug)]
pub enum Pattern {
    All(String),
    NaturalNumber(String),
    Pair {
        first: Box<Ranged<Pattern>>,
        second: Box<Ranged<Pattern>>,
    },
}

#[derive(Clone, Copy, Debug)]
pub enum BinaryOp {
    Addition,
    Multiplication,
    Pairing,
}

impl std::fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Addition => write!(f, "+"),
            Self::Multiplication => write!(f, "*"),
            Self::Pairing => write!(f, ":"),
        }
    }
}

impl From<&Token> for BinaryOp {
    fn from(val: &Token) -> Self {
        match val {
            Token::Asterisk => Self::Multiplication,
            Token::Plus => Self::Addition,
            Token::Colon => Self::Pairing,
            _ => unreachable!(),
        }
    }
}

#[derive(PartialEq)]
enum Associativity {
    Right,
    Left,
    #[allow(unused)]
    None,
}
