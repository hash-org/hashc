//! Hash compiler parser error data types.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use hash_ast::{
    error::ParseError,
    location::{Location, SourceLocation},
    module::ModuleIdx,
};

use crate::token::{Delimiter, TokenAtom, TokenKindVector};

/// A [TokenError] represents a encountered error during tokenisation, which includes an optional message
/// with the error, the [TokenErrorKind] which classifies the error, and a [Location] that represents
/// where the tokenisation error occurred.
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
    Expected(TokenAtom),
    /// Unclosed tree block
    Unclosed(Delimiter),
}

/// Utility methods for [TokenError]
impl TokenError {
    /// Create a new [TokenError] from a message, kind and a span location.
    pub fn new(message: Option<String>, kind: TokenErrorKind, location: Location) -> Self {
        TokenError {
            message,
            kind,
            location,
        }
    }

    /// Convert a [TokenError] into a printable message.
    pub fn as_message(&self) -> String {
        let sub_message = match self.kind {
            TokenErrorKind::BadEscapeSequence => "Invalid character escape sequence.".to_owned(),
            TokenErrorKind::MalformedNumericalLiteral => "Malformed numerical literal.".to_owned(),
            TokenErrorKind::Unexpected(ch) => {
                format!("Encountered unexpected character '{}'", ch)
            }
            TokenErrorKind::Expected(atom) => format!("Expected token '{}' here.", atom),
            TokenErrorKind::Unclosed(delim) => {
                format!("Encountered unclosed delimiter '{}'", delim)
            }
        };

        match &self.message {
            Some(message) => {
                let copy = message.to_owned();
                format!("{} {}", copy, sub_message)
            }
            None => sub_message,
        }
    }
}

/// This implementation exists since we can't use tuples that are un-named
/// with foreign module types.
pub struct TokenErrorWrapper(pub ModuleIdx, pub TokenError);

impl From<TokenErrorWrapper> for ParseError {
    fn from(TokenErrorWrapper(idx, err): TokenErrorWrapper) -> Self {
        ParseError::Parsing {
            message: err.as_message(),
            src: SourceLocation {
                location: err.location,
                module_index: idx,
            },
        }
    }
}

/// A GeneratorError represents possible errors that occur when transforming the token
/// stream into the AST.
pub struct AstGenError<'a> {
    kind: GeneratorErrorKind,
    location: SourceLocation,
    expected: Option<TokenKindVector<'a>>,
    received: Option<TokenAtom>,
}

/// Utility methods for creating AstGenErrors
impl<'a> AstGenError<'a> {
    pub fn new(
        kind: GeneratorErrorKind,
        expected: Option<TokenKindVector<'a>>, // @@Nocheckin: maybe make this a TokenKindVector for multiple options?
        received: Option<TokenAtom>,
        location: SourceLocation,
    ) -> Self {
        Self {
            kind,
            expected,
            location,
            received,
        }
    }
}

pub enum ExpectedTyArguments {
    Struct,
    Enum,
}

pub enum GeneratorErrorKind {
    Keyword,
    Atom,
    Either,

    /// Nocheckin:
    /// Expecting ';' at the end of a statement, but got
    Expected,

    /// "Expected block body, which begins with a '{', but reached end of input",
    /// "Expected block body, which begins with a '{{' but got a {}",
    Block,
    EOF,
    ReAssignmentOp,

    /// NOCHECKIN:
    /// 1. Expected struct type args or struct definition entries here"
    /// 2. Expected Enum type args or struct definition entries here"
    TypeArguments(ExpectedTyArguments),

    /// Expected statement.
    ExpectedStatement,

    /// Expected an expression.
    ExpectedExpression,

    /// "Expected an arrow '=>' here."
    ExpectedArrow,

    /// "Expected an arrow '=>' after type arguments denoting a function type.",
    ExpectedFnArrow,

    /// Expected a function body here.
    ExpectedFnBody,

    /// "Expected a type here."
    ExpectedType,

    /// "Expected field name or an infix function call"
    /// "Expecting field name after property access.")
    InfixCall,

    /// Expected an import path.
    ImportPath,

    ///  "Expected identifier after a name access qualifier"
    AccessName,
}

/// This implementation exists since we can't use tuples that are un-named
/// with foreign module types.
pub struct GeneratorErrorWrapper<'a>(pub ModuleIdx, pub AstGenError<'a>);

impl<'a> From<AstGenError<'a>> for ParseError {
    fn from(_: AstGenError) -> Self {
        todo!()
    }
}

// impl<'a, T> From<AstGenResult<'a, T>> for ParseResult<T> {
//     fn from(_: AstGenError) -> Self {
//         todo!()
//     }
// }

impl<'a> From<ParseError> for AstGenError<'a> {
    fn from(_: ParseError) -> Self {
        todo!()
    }
}
