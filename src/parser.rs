use std::iter::Peekable;

use crate::{
    ranged::Ranged,
    tokens::{Token, TokenError, Tokens},
};

const BINARY_OPERATORS: [(Token, Associativity, usize); 3] = [
    (Token::Colon, Associativity::Right, 0),
    (Token::Plus, Associativity::Left, 1),
    (Token::Asterisk, Associativity::Left, 2),
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

    #[allow(clippy::needless_pass_by_value)]
    fn expect(&mut self, expected: Token) -> ParseResult<()> {
        match self.tokens.next() {
            Some(token_result) => {
                let (token, start, end) = token_result?.into_tuple();

                if token == expected {
                    Ok(Ranged::new((), start, end))
                } else {
                    Err(Ranged::new(ParseError::UnexpectedToken(token), start, end))
                }
            }
            None => Err(Ranged::new(ParseError::UnexpectedEOF, 0, 0)),
        }
    }

    fn expect_ident(&mut self) -> ParseResult<String> {
        match self.tokens.next() {
            Some(token_result) => {
                let (token, start, end) = token_result?.into_tuple();

                if let Token::Identifier(name) = token {
                    Ok(Ranged::new(name, start, end))
                } else {
                    Err(Ranged::new(ParseError::UnexpectedToken(token), start, end))
                }
            }
            None => Err(Ranged::new(ParseError::UnexpectedEOF, 0, 0)),
        }
    }

    fn primary_pattern(&mut self) -> ParseResult<Pattern> {
        let Some(token_result) = self.tokens.next() else {
            return Err(Ranged::new(ParseError::UnexpectedEOF, 0, 0));
        };

        let (token, start, end) = token_result?.into_tuple();

        match token {
            Token::Identifier(ident) => Ok(Ranged::new(Pattern::All(ident), start, end)),
            Token::NaturalNumber(nat) => Ok(Ranged::new(Pattern::NaturalNumber(nat), start, end)),
            Token::OpeningParenthesis => {
                let (pattern, _, _) = self.pattern()?.into_tuple();
                let ((), _, end) = self.expect(Token::ClosingParenthesis)?.into_tuple();
                Ok(Ranged::new(pattern, start, end))
            }
            unexpected => Err(Ranged::new(
                ParseError::UnexpectedToken(unexpected),
                start,
                end,
            )),
        }
    }

    fn pair_pattern(&mut self) -> ParseResult<Pattern> {
        let primary = self.primary_pattern()?;

        if let Some(token_result) = self.tokens.peek() {
            let (Token::Colon, _, _) = token_result.as_ref()?.as_tuple() else {
                return Ok(primary);
            };

            self.tokens.next();
            let second = self.pair_pattern()?;

            let start = primary.start;
            let end = second.end;
            return Ok(Ranged::new(
                Pattern::Pair {
                    first: Box::new(primary),
                    second: Box::new(second),
                },
                start,
                end,
            ));
        }

        Ok(primary)
    }

    fn pattern(&mut self) -> ParseResult<Pattern> {
        self.pair_pattern()
    }

    fn primary(&mut self) -> ParseResult<Expression> {
        let Some(token_result) = self.tokens.next() else {
            return Err(Ranged::new(ParseError::UnexpectedEOF, 0, 0));
        };

        let (token, start, end) = token_result?.into_tuple();

        match token {
            Token::Identifier(ident) => Ok(Ranged::new(Expression::Identifier(ident), start, end)),
            Token::NaturalNumber(nat) => {
                Ok(Ranged::new(Expression::NaturalNumber(nat), start, end))
            }
            Token::OpeningParenthesis => {
                let (expr, _, _) = self.expression()?.into_tuple();
                let ((), _, end) = self.expect(Token::ClosingParenthesis)?.into_tuple();
                Ok(Ranged::new(expr, start, end))
            }
            Token::LetKeyword => {
                let pattern = self.pattern()?;
                self.expect(Token::Equals)?;
                let vexpr = Box::new(self.expression()?);
                self.expect(Token::InKeyword)?;
                let rexpr = Box::new(self.expression()?);
                let end = rexpr.end;
                Ok(Ranged::new(
                    Expression::Let {
                        pattern,
                        vexpr,
                        rexpr,
                    },
                    start,
                    end,
                ))
            }
            Token::FunKeyword => {
                self.expect(Token::OpeningParenthesis)?;

                let mut arguments = vec![];
                if let Some(token_result) = self.tokens.peek() {
                    if !matches!(token_result.as_ref()?.data, Token::ClosingParenthesis) {
                        arguments.push(self.pattern()?);
                        while let Some(token_result) = self.tokens.peek() {
                            if let (Token::ClosingParenthesis, _, _) = token_result.as_ref()?.as_tuple() {
                                break;
                            };
                            self.expect(Token::Comma)?;
                            arguments.push(self.pattern()?);
                        }
                    }
                }
                self.expect(Token::ClosingParenthesis)?;
                let expr = Box::new(self.expression()?);
                let end = expr.end;
                Ok(Ranged::new(
                    Expression::Function { arguments, expr },
                    start,
                    end,
                ))
            }
            Token::ImportKeyword => {
                let ident = self.expect_ident()?;
                let mut end = ident.end;
                let mut parts = vec![ident.data];
                while let Some(token_result) = self.tokens.peek() {
                    let Token::Dot = token_result.as_ref()?.data else {
                        break
                    };
                    self.tokens.next();
                    let ident = self.expect_ident()?;
                    end = ident.end;
                    parts.push(ident.data);
                }
                Ok(Ranged::new(Expression::Import(parts), start, end))
            }
            unexpected => Err(Ranged::new(
                ParseError::UnexpectedToken(unexpected),
                start,
                end,
            )),
        }
    }

    fn application_and_access(&mut self) -> ParseResult<Expression> {
        let mut primary = self.primary()?;

        while let Some(token_result) = self.tokens.peek() {
            let token = &token_result.as_ref()?.data;
            match token {
                Token::OpeningParenthesis => {
                    self.tokens.next();

                    let mut arguments = vec![];
                    if let Some(token_result) = self.tokens.peek() {
                        if !matches!(token_result.as_ref()?.data, Token::ClosingParenthesis) {
                            arguments.push(self.expression()?);
                            while let Some(token_result) = self.tokens.peek() {
                                if let (Token::ClosingParenthesis, _, _) = token_result.as_ref()?.as_tuple()
                                {
                                    break;
                                };
                                self.expect(Token::Comma)?;
                                arguments.push(self.expression()?);
                            }
                        }
                    }
                    let ((), _, end) = self.expect(Token::ClosingParenthesis)?.into_tuple();
                    let start = primary.start;

                    primary = Ranged::new(
                        Expression::Application {
                            expr: Box::new(primary),
                            arguments,
                        },
                        start,
                        end,
                    );
                }
                Token::Dot => {
                    self.tokens.next();
                    let what = self.expect_ident()?;
                    let start = primary.start;
                    let end = what.end;
                    primary = Ranged::new(Expression::Access { from: Box::new(primary), what }, start, end)
                }
                _ => break
            }
        }

        Ok(primary)
    }

    fn binary(&mut self, min_prec: usize) -> ParseResult<Expression> {
        let mut expr = self.application_and_access()?;

        while let Some(token_result) = self.tokens.peek() {
            let (token, _, _) = token_result.as_ref()?.as_tuple();

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

            let start = expr.start;
            let end = rhs.end;
            expr = Ranged::new(
                Expression::Binary {
                    lhs: Box::new(expr),
                    rhs: Box::new(rhs),
                    bop,
                },
                start,
                end,
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
        let (expr, start, end) = self.expression()?.into_tuple();

        match self.tokens.next() {
            Some(token_result) => {
                let (_, start, _) = token_result?.into_tuple();
                Err(Ranged::new(ParseError::Unconsumed, start, 0))
            }
            None => Ok(Ranged::new(expr, start, end)),
        }
    }

    pub fn parse_module(&mut self) -> ParseResult<Vec<(String, Ranged<Expression>)>> {
        let mut definitions = vec![];
        while let Some(token_result) = self.tokens.next() {
            let (token, start, end) = token_result?.into_tuple();
            let Token::Identifier(name) = token else {
                return Err(Ranged::new(ParseError::UnexpectedToken(token), start, end));
            };
            self.expect(Token::Equals)?;
            definitions.push((name, self.expression()?))
        }

        Ok(Ranged::new(definitions, 0, 0))
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
        let (data, start, end) = value.into_tuple();
        Self::new(ParseError::TokenError(data), start, end)
    }
}

impl From<&Ranged<TokenError>> for Ranged<ParseError> {
    fn from(value: &Ranged<TokenError>) -> Self {
        let (data, start, end) = value.as_tuple();
        Self::new(ParseError::TokenError(data.clone()), *start, *end)
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
        vexpr: Box<Ranged<Expression>>,
        rexpr: Box<Ranged<Expression>>,
    },
    Function {
        arguments: Vec<Ranged<Pattern>>,
        expr: Box<Ranged<Expression>>,
    },
    Application {
        expr: Box<Ranged<Expression>>,
        arguments: Vec<Ranged<Expression>>,
    },
    Access {
        from: Box<Ranged<Expression>>,
        what: Ranged<String>,
    },
    Import(Vec<String>)
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
