//! File describing all the variants of Tokens that can be present within a
//! Hash source file.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use std::fmt;

use crate::caching::{StringIdentifier, STRING_LITERAL_MAP};
use hash_ast::ident::Identifier;
use hash_ast::ident::IDENTIFIER_MAP;
use hash_ast::location::Location;

pub type TokenResult<T> = Result<T, TokenError>;

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
            TokenKind::Ident(ident) => write!(f, "Ident ({})", IDENTIFIER_MAP.ident_name(*ident)),
            TokenKind::StrLiteral(literal) => {
                write!(f, "StringLiteral ({})", STRING_LITERAL_MAP.lookup(*literal))
            }
            TokenKind::CharLiteral(ch) => {
                write!(f, "CharLiteral ({})", ch)
            }
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
    /// Integer Literal
    IntLiteral(u64),
    /// Float literal
    FloatLiteral(f64),
    /// Character literal
    CharLiteral(char),
    /// StrLiteral,
    StrLiteral(StringIdentifier),
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
    /// "'"
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

#[derive(Debug)]
pub struct TokenError {
    pub(crate) message: Option<String>,
    kind: TokenErrorKind,
    location: Location,
}

#[derive(Debug)]
pub enum TokenErrorKind {
    BadEscapeSequence,
    MalformedNumericalLiteral,
    Unexpected(char),
    Expected(TokenKind),
}

impl TokenError {
    pub fn new(message: Option<String>, kind: TokenErrorKind, location: Location) -> Self {
        TokenError {
            message,
            kind,
            location,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        println!("token      ={:?}", std::mem::size_of::<Token>());
        println!("token_kind ={:?}", std::mem::size_of::<TokenKind>());
    }
}
