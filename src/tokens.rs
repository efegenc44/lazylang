use std::{
    iter::{Enumerate, Peekable},
    str::Chars,
};

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
}

impl Iterator for Tokens<'_> {
    type Item = (Result<Token, TokenError>, usize, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let Some(&(start, ch)) = self.chars.peek() else {
            return None;
        };

        if ch.is_whitespace() {
            self.chars.next();
            return self.next();
        }

        if ch.is_ascii_digit() {
            return Some((Ok(self.number()), start, self.peek_index()));
        }

        let result = match ch {
            '(' => Ok(Token::OpeningParenthesis),
            ')' => Ok(Token::ClosingParenthesis),
            '*' => Ok(Token::Asterisk),
            '+' => Ok(Token::Plus),
            _ => Err(TokenError::UnknownStartOfAToken(ch)),
        };
        self.chars.next();

        Some((result, start, self.peek_index()))
    }
}

#[derive(Debug)]
pub enum Token {
    NaturalNumber(String),
    OpeningParenthesis,
    ClosingParenthesis,
    Asterisk,
    Plus,
}

#[derive(Debug)]
pub enum TokenError {
    UnknownStartOfAToken(char),
}
