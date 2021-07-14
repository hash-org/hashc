//! Hash compiler low level implementation for the language lexer. Convert
//! an arbitrary string into a sequence of Lexemes.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use hash_ast::location::Location;

use crate::idents::*;
use crate::token::Token;
use crate::token::TokenKind;
use std::str::Chars;

pub(crate) struct Lexer<'a> {
    length: usize,
    offset: usize,
    contents: Chars<'a>,
}

const EOF_CHAR: char = '\0';

impl<'a> Lexer<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        Lexer {
            length: input.len(),
            offset: 0,
            contents: input.chars(),
        }
    }

    /// Returns a `Chars` iterator over the remaining characters.
    fn chars(&self) -> Chars<'a> {
        self.contents.clone()
    }

    /// Returns amount of already consumed symbols.
    pub(crate) fn len_consumed(&self) -> usize {
        self.length - self.offset //- self.contents.as_str().len()
    }

    /// Peeks the next symbol from the input stream without consuming it.
    pub(crate) fn first(&self) -> char {
        self.nth_char(0)
    }

    /// Peeks the second symbol from the input stream without consuming it.
    pub(crate) fn second(&self) -> char {
        self.nth_char(1)
    }

    /// Moves to the next character.
    pub(crate) fn next(&mut self) -> Option<char> {
        let c = self.contents.next()?;

        // only increment the offset by one if there is a next character
        self.offset += 1;
        Some(c)
    }

    /// Returns nth character relative to the current position.
    /// If requested position doesn't exist, `EOF_CHAR` is returned.
    /// However, getting `EOF_CHAR` doesn't always mean actual end of file,
    /// it should be checked with `is_eof` method.
    fn nth_char(&self, n: usize) -> char {
        self.chars().nth(n).unwrap_or(EOF_CHAR)
    }

    /// Checks if there is nothing more to consume.
    pub(crate) fn is_eof(&self) -> bool {
        self.contents.as_str().is_empty()
    }

    /// Parses a token from the input string.
    pub(crate) fn advance_token(&mut self) -> Token {
        let token_kind = loop {
            let next_char = self.next().unwrap();

            match next_char {
                // Slash, comment or block comment.
                '/' => {
                    break match self.first() {
                        '/' => self.line_comment(),
                        '*' => self.block_comment(),
                        _ => TokenKind::Slash,
                    }
                }

                // Whitespace sequence.
                c if c.is_whitespace() => continue,

                // One-symbol tokens.
                ';' => break TokenKind::Semi,
                ',' => break TokenKind::Comma,
                '.' => break TokenKind::Dot,
                '(' => break TokenKind::OpenParen,
                ')' => break TokenKind::CloseParen,
                '{' => break TokenKind::OpenBrace,
                '}' => break TokenKind::CloseBrace,
                '[' => break TokenKind::OpenBracket,
                ']' => break TokenKind::CloseBracket,
                // '@' => TokenKind::At,
                // '#' => TokenKind::Pound,
                '~' => break TokenKind::Tilde,
                // '?' => TokenKind::Question,
                ':' => break TokenKind::Colon,
                // '$' => TokenKind::Dollar,
                '=' => break TokenKind::Eq,
                '!' => break TokenKind::Exclamation,
                '<' => break TokenKind::Lt,
                '>' => break TokenKind::Gt,
                '-' => break TokenKind::Minus,
                '&' => break TokenKind::And,
                '|' => break TokenKind::Pipe,
                '+' => break TokenKind::Plus,
                '*' => break TokenKind::Star,
                '^' => break TokenKind::Caret,
                '%' => break TokenKind::Percent,

                // Identifier (this should be checked after other variant that can
                // start as identifier).
                c if is_id_start(c) => break self.ident(),

                // Numeric literal.
                '0'..='9' => break self.number(),

                // character literal.
                '\'' => break self.char(),

                // String literal.
                '"' => break self.string(),

                _ => break TokenKind::Unexpected,
            }
        };

        let location = Location::span(self.offset, self.len_consumed());
        Token::new(token_kind, location)
    }

    /// Consume an identifier, at this stage keywords are also considered to be identfiers
    pub(crate) fn ident(&mut self) -> TokenKind {
        todo!()
    }

    pub(crate) fn number(&mut self) -> TokenKind {
        todo!()
    }

    pub(crate) fn char(&mut self) -> TokenKind {
        todo!()
    }

    pub(crate) fn string(&mut self) -> TokenKind {
        todo!()
    }

    /// Consume a line comment after the first folloing slash, essentially eating
    /// characters up to the next '\n' encountered. If we reach EOF before a newline, then
    /// we stop eating there.
    pub(crate) fn line_comment(&mut self) -> TokenKind {
        todo!()
    }

    /// Consume a block comment after the first following '/*' sequence of characters. If the
    /// iterator encounters the start of another block comment, we increment a nested comment
    /// counter to ensure that nested block comments are accounted for and handeled gracefully.
    pub(crate) fn block_comment(&mut self) -> TokenKind {
        todo!()
    }
}

/// Parses the first token from the provided input string.
pub fn first_token(input: &str) -> Token {
    debug_assert!(!input.is_empty());
    Lexer::new(input).advance_token()
}

pub fn tokenise(mut input: &str) -> impl Iterator<Item = Token> + '_ {
    std::iter::from_fn(move || {
        if input.is_empty() {
            return None;
        }
        let token = first_token(input);
        input = &input[token.span.size()..];
        Some(token)
    })
}
