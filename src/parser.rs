use core::fmt;
use std::{iter::Peekable, result};

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

    fn peek_token(&mut self) -> ParseResult<&Token> {
        Ok(self
            .tokens
            .peek()
            .map(result::Result::as_ref)
            .ok_or_else(|| Ranged::new(ParseError::UnexpectedEOF, Default::default()))?
            .map(Ranged::as_ref)?)
    }

    fn next_token(&mut self) -> ParseResult<Token> {
        Ok(self
            .tokens
            .next()
            .ok_or_else(|| Ranged::new(ParseError::UnexpectedEOF, Default::default()))??)
    }

    #[allow(clippy::needless_pass_by_value)]
    fn expect(&mut self, expected: Token) -> ParseResult<()> {
        let (token, ranges) = self.next_token()?.into_tuple();
        if token == expected {
            Ok(Ranged::new((), ranges))
        } else {
            Err(Ranged::new(ParseError::UnexpectedToken(token), ranges))
        }
    }

    fn expect_ident(&mut self) -> ParseResult<String> {
        let (token, ranges) = self.next_token()?.into_tuple();
        if let Token::Identifier(name) = token {
            Ok(Ranged::new(name, ranges))
        } else {
            Err(Ranged::new(ParseError::UnexpectedToken(token), ranges))
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    fn optional(&mut self, optional: Token) -> bool {
        self.peek_token()
            .map(|token| token.data)
            .map_or(false, |token| token == &optional)
    }

    fn parse_pattern_grouping(&mut self) -> ParseResult<Pattern> {
        let starts = self.expect(Token::OpeningParenthesis).unwrap().starts();
        let pattern = self.pattern()?.data;
        let ends = self.expect(Token::ClosingParenthesis)?.ends();

        Ok(Ranged::new(pattern, (starts, ends)))
    }

    fn primary_pattern(&mut self) -> ParseResult<Pattern> {
        match self.peek_token()?.data {
            Token::OpeningParenthesis => self.parse_pattern_grouping(),
            _ => {
                let (token, ranges) = self.tokens.next().unwrap().unwrap().into_tuple();
                match token {
                    Token::Identifier(ident) => Ok(Ranged::new(Pattern::All(ident), ranges)),
                    Token::NaturalNumber(nat) => {
                        Ok(Ranged::new(Pattern::NaturalNumber(nat), ranges))
                    }
                    unexpected => Err(Ranged::new(ParseError::UnexpectedToken(unexpected), ranges)),
                }
            }
        }
    }

    fn pair_pattern(&mut self) -> ParseResult<Pattern> {
        let primary = self.primary_pattern()?;

        if self.optional(Token::Colon) {
            self.tokens.next();
            let second = self.pair_pattern()?;
            let starts = primary.starts();
            let ends = second.ends();
            Ok(Ranged::new(
                Pattern::Pair {
                    first: Box::new(primary),
                    second: Box::new(second),
                },
                (starts, ends),
            ))
        } else {
            Ok(primary)
        }
    }

    fn or_pattern(&mut self) -> ParseResult<Pattern> {
        let mut pattern = self.pair_pattern()?;

        while self.optional(Token::Comma) {
            self.tokens.next();
            let left = self.pair_pattern()?;
            let starts = pattern.starts();
            let ends = left.ends();
            pattern = Ranged::new(
                Pattern::Or {
                    right: Box::new(pattern),
                    left: Box::new(left),
                },
                (starts, ends),
            );
        }

        Ok(pattern)
    }

    fn pattern(&mut self) -> ParseResult<Pattern> {
        self.or_pattern()
    }

    fn parse_grouping(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::OpeningParenthesis).unwrap().starts();
        let expr = self.expression()?.data;
        let ends = self.expect(Token::ClosingParenthesis)?.ends();

        Ok(Ranged::new(expr, (starts, ends)))
    }

    fn parse_let(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::LetKeyword).unwrap().starts();
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

    fn parse_lambda(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::Backslash).unwrap().starts();
        let mut args = vec![];
        if !self.optional(Token::Arrow) {
            args.push(self.pattern()?);
            while !self.optional(Token::Arrow) {
                self.expect(Token::Comma)?;
                args.push(self.pattern()?);
            }
        }
        self.expect(Token::Arrow)?;
        let expr = Box::new(self.expression()?);
        let ends = expr.ends();

        Ok(Ranged::new(
            Expression::Function { args, expr },
            (starts, ends),
        ))
    }

    fn parse_import(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::ImportKeyword).unwrap().starts();
        let part = self.expect_ident()?;
        let mut ends = part.ends();
        let mut parts = vec![part.data];
        while self.optional(Token::Dot) {
            self.tokens.next();
            let part = self.expect_ident()?;
            ends = part.ends();
            parts.push(part.data);
        }

        Ok(Ranged::new(Expression::Import(parts), (starts, ends)))
    }

    fn parse_match(&mut self) -> ParseResult<Expression> {
        let starts = self.expect(Token::MatchKeyword).unwrap().starts();
        let expr = Box::new(self.expression()?);

        self.expect(Token::Bar).unwrap();
        let pattern = self.pattern()?;
        self.expect(Token::Arrow).unwrap();
        let branch_expr = Box::new(self.expression()?);
        let mut ends = branch_expr.ends();

        let mut branches = vec![(pattern, branch_expr)];
        while self.optional(Token::Bar) {
            self.tokens.next();
            let pattern = self.pattern()?;
            self.expect(Token::Arrow).unwrap();
            let expr = Box::new(self.expression()?);
            ends = expr.ends();
            branches.push((pattern, expr));
        }

        Ok(Ranged::new(
            Expression::Match { expr, branches },
            (starts, ends),
        ))
    }

    fn primary(&mut self) -> ParseResult<Expression> {
        match self.peek_token()?.data {
            Token::OpeningParenthesis => self.parse_grouping(),
            Token::LetKeyword => self.parse_let(),
            Token::Backslash => self.parse_lambda(),
            Token::ImportKeyword => self.parse_import(),
            Token::MatchKeyword => self.parse_match(),
            _ => {
                let (token, ranges) = self.tokens.next().unwrap().unwrap().into_tuple();
                match token {
                    Token::Identifier(ident) => {
                        Ok(Ranged::new(Expression::Identifier(ident), ranges))
                    }
                    Token::NaturalNumber(nat) => {
                        Ok(Ranged::new(Expression::NaturalNumber(nat), ranges))
                    }
                    unexpected => Err(Ranged::new(ParseError::UnexpectedToken(unexpected), ranges)),
                }
            }
        }
    }

    fn application_and_access(&mut self) -> ParseResult<Expression> {
        let mut expr = self.primary()?;

        while let Some(token_result) = self.tokens.peek() {
            match &token_result.as_ref()?.data {
                Token::OpeningParenthesis => {
                    self.tokens.next();
                    let mut args = vec![];
                    if !self.optional(Token::ClosingParenthesis) {
                        args.push(self.expression()?);
                        while !self.optional(Token::ClosingParenthesis) {
                            self.expect(Token::Comma)?;
                            args.push(self.expression()?);
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
            Some(token_result) => Err(Ranged::new(ParseError::Unconsumed, token_result?.ranges())),
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
            Self::Unconsumed => write!(f, "From here, the rest couldn't be consumed."),
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
    pub fn report(&self, source_name: &str, source: &str) {
        if matches!(self.data, ParseError::UnexpectedEOF) {
            todo!()
        }

        error::report(self, source_name, source, "parsing");
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
    Match {
        expr: Box<Ranged<Expression>>,
        branches: Vec<(Ranged<Pattern>, Box<Ranged<Expression>>)>,
    },
}

#[derive(Clone, Debug)]
pub enum Pattern {
    All(String),
    NaturalNumber(String),
    Pair {
        first: Box<Ranged<Pattern>>,
        second: Box<Ranged<Pattern>>,
    },
    Or {
        right: Box<Ranged<Pattern>>,
        left: Box<Ranged<Pattern>>,
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
