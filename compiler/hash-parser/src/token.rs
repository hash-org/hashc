//! File describing all the variants of Tokens that can be present within a
//! Hash source file.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]

use hash_ast::ident::Identifier;
use hash_ast::location::Location;

#[derive(Debug)]
pub enum TokenError {
    Unexpected(char),
    Expected(TokenKind),
}

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

#[derive(Debug, Copy, Clone)]
pub enum LiteralKind {
    Float,
    Int,
    String,
    Char,
}

#[repr(packed(1))]
#[derive(Debug, Copy, Clone)]
pub struct Lit {
    symbol: Identifier, // @@TODO: change this to a symbol type which could
    kind: LiteralKind,
}
#[derive(Debug)]
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

    /// Literal with variants of a [LiteralKind]
    Literal(Lit),
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

    // '@'
    // At,
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
        println!("kind={:?}", std::mem::size_of::<Lit>());
        println!("token={:?}", std::mem::size_of::<TokenKind>());
    }
}
