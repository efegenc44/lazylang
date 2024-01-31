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
    type Item = Result<(Token, usize, usize), (TokenError, usize, usize)>;

    fn next(&mut self) -> Option<Self::Item> {
        let Some(&(start, ch)) = self.chars.peek() else {
            return None;
        };

        if ch.is_whitespace() {
            self.chars.next();
            return self.next();
        }

        if ch.is_ascii_digit() {
            return Some(Ok((self.number(), start, self.peek_index())));
        }

        self.chars.next();
        let token = match ch {
            '(' => Token::OpeningParenthesis,
            ')' => Token::ClosingParenthesis,
            '*' => Token::Asterisk,
            '^' => Token::Caret,
            '+' => Token::Plus,
            _ => {
                return Some(Err((
                    TokenError::UnknownStartOfAToken(ch),
                    start,
                    self.peek_index(),
                )))
            }
        };

        Some(Ok((token, start, self.peek_index())))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    NaturalNumber(String),
    OpeningParenthesis,
    ClosingParenthesis,
    Asterisk,
    Caret,
    Plus,
}

#[derive(Clone, Debug)]
pub enum TokenError {
    UnknownStartOfAToken(char),
}
