use std::{
    iter::{Enumerate, Peekable},
    str::Chars,
};

use crate::ranged::Ranged;

pub struct Tokens<'source> {
    chars: Peekable<Enumerate<Chars<'source>>>,
}

impl<'source> Tokens<'source> {
    pub fn new(source: &'source str) -> Self {
        Self {
            chars: source.chars().enumerate().peekable(),
        }
    }

    fn peek_index(&mut self) -> usize {
        self.chars.peek().map_or(0, |(end, _)| *end)
    }

    fn number(&mut self) -> Token {
        let mut number = String::new();
        while let Some((_, ch)) = self.chars.next_if(|(_, ch)| ch.is_ascii_digit()) {
            number.push(ch);
        }

        Token::NaturalNumber(number)
    }

    fn symbol(&mut self) -> Token {
        let mut symbol = String::new();
        while let Some((_, ch)) = self.chars.next_if(|(_, ch)| ch.is_alphanumeric()) {
            symbol.push(ch);
        }

        match symbol.as_str() {
            "let" => Token::LetKeyword,
            "in" => Token::InKeyword,
            "fun" => Token::FunKeyword,
            "import" => Token::ImportKeyword,
            _ => Token::Identifier(symbol),
        }
    }
}

impl Iterator for Tokens<'_> {
    type Item = Result<Ranged<Token>, Ranged<TokenError>>;

    fn next(&mut self) -> Option<Self::Item> {
        let Some(&(start, ch)) = self.chars.peek() else {
            return None;
        };

        if ch.is_whitespace() {
            self.chars.next();
            return self.next();
        }

        if ch.is_alphabetic() {
            return Some(Ok(Ranged::new(self.symbol(), start, self.peek_index())));
        }

        if ch.is_ascii_digit() {
            return Some(Ok(Ranged::new(self.number(), start, self.peek_index())));
        }

        self.chars.next();
        let token = match ch {
            '(' => Token::OpeningParenthesis,
            ')' => Token::ClosingParenthesis,
            '*' => Token::Asterisk,
            '=' => Token::Equals,
            ':' => Token::Colon,
            ',' => Token::Comma,
            '+' => Token::Plus,
            '.' => Token::Dot,
            _ => {
                return Some(Err(Ranged::new(
                    TokenError::UnknownStartOfAToken(ch),
                    start,
                    self.peek_index(),
                )))
            }
        };

        Some(Ok(Ranged::new(token, start, self.peek_index())))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    Identifier(String),
    NaturalNumber(String),
    OpeningParenthesis,
    ClosingParenthesis,
    Asterisk,
    Equals,
    Colon,
    Comma,
    Plus,
    Dot,
    LetKeyword,
    InKeyword,
    FunKeyword,
    ImportKeyword,
}

#[derive(Clone, Debug)]
pub enum TokenError {
    UnknownStartOfAToken(char),
}
