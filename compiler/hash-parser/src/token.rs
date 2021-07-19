//! File describing all the variants of Tokens that can be present within a
//! Hash source file.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use std::fmt;

use hash_ast::ident::Identifier;
use hash_ast::ident::IDENTIFIER_MAP;
use hash_ast::location::Location;

#[derive(Debug)]
pub enum TokenError {
    Unexpected(char),
    Expected(TokenKind),
}

/// A Lexeme token that represents the smallest code unit of a hash source file. The
/// token contains a kind which is elaborated by [TokenKind] and a [Location] in the
/// source that is represented as a span. The span is the beginning byte offset, and the
/// number of bytes for the said token.
#[derive(Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Location,
}

impl Token {
    pub fn new(kind: TokenKind, span: Location) -> Self {
        Token { kind, span }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            // @@TODO: actually implement proper display for when identifiers and literal format storage is finalised.
            TokenKind::Ident(ident) => write!(f, "Ident ({})", IDENTIFIER_MAP.ident_name(*ident)),
            kind => write!(f, "{:?}", kind),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum TokenKind {
    /// '='
    Eq,
    /// '<'
    Lt,
    /// '>'
    Gt,
    /// '+'
    Plus,
    /// '-'
    Minus,
    /// *
    Star,
    /// '/'
    Slash,
    /// '%'
    Percent,
    /// '^'
    Caret,

    /// '&'
    And,

    // // @@REMOVE ME
    // IntLiteral,
    // FloatLiteral,
    // CharLiteral,
    // StrLiteral,

    IntLiteral(u64),
    FloatLiteral(f64),
    CharLiteral(char),
    StrLiteral,
    // StrLiteral(String),
    /// Identifier
    Ident(Identifier),
    /// '~'
    Tilde,
    /// '|'
    Pipe,
    /// '!'
    Exclamation,
    /// '.'
    Dot,
    /// ':'
    Colon,
    /// ';'
    Semi,
    /// ','
    Comma,
    /// '"'
    Quote,
    // "'"
    SingleQoute,
    /// '{'
    OpenBrace,
    /// '('
    OpenParen,
    /// '['
    OpenBracket,
    /// '}'
    CloseBrace,
    /// ')'
    CloseParen,
    /// ']'
    CloseBracket,

    /// A token that was unexpected by the lexer, e.g. a unicode symbol not within
    /// string literal.
    Unexpected,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        // println!("kind={:?}", std::mem::size_of::<Lit>());
        println!("token={:?}", std::mem::size_of::<TokenKind>());
    }
}
