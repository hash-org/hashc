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
                write!(
                    f,
                    "StringLiteral (\"{}\")",
                    STRING_LITERAL_MAP.lookup(*literal)
                )
            }
            // We want to print the actual character, instead of a potential escape code
            TokenKind::CharLiteral(ch) => {
                write!(f, "CharLiteral ('{}')", ch)
            }
            kind => write!(f, "{:?}", kind),
        }
    }
}

/// A TokenKind represents all variants of a token that can be present in a source file. Must of the
/// kinds only represen a single character, but some tokens account for an entire literal or an identifier.
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

/// A [TokenError] represents a encountered error during tokenisation, which includes an optional message
/// with the error, the [TokenErrorKind] which classifies the error, and a [ast::Location] that represents
/// where the tokenisation error occured.
#[derive(Debug)]
pub struct TokenError {
    pub(crate) message: Option<String>,
    kind: TokenErrorKind,
    location: Location,
}

/// A [TokenErrorKind] represents the kind of [TokenError] which gives additional context to the error
/// with the provided message in [TokenError]
#[derive(Debug)]
pub enum TokenErrorKind {
    /// Occurs when a escape sequence (within a character or a string) is malformed.
    BadEscapeSequence,
    /// Occurs when a numerical literal doesn't follow the language specification, or is too large.
    MalformedNumericalLiteral,
    /// Occurs when a char is unexpected in the current context
    Unexpected(char),
    /// Occurs when the tokeniser expects a particular token next, but could not derive one.
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
