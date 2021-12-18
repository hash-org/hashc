//! Hash compiler parser error data types.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use hash_ast::{
    error::{ImportError, ParseError},
    location::{Location, SourceLocation},
    module::ModuleIdx,
};

use crate::token::{Delimiter, TokenKind, TokenKindVector};
use derive_more::Constructor;
use thiserror::Error;

/// A [TokenError] represents a encountered error during tokenisation, which includes an optional message
/// with the error, the [TokenErrorKind] which classifies the error, and a [Location] that represents
/// where the tokenisation error occurred.
#[derive(Debug, Constructor, Error)]
#[error("{} {kind}", .message.as_ref().unwrap_or(&String::from("")))]
pub struct TokenError {
    pub(crate) message: Option<String>,
    kind: TokenErrorKind,
    location: Location,
}

/// A [TokenErrorKind] represents the kind of [TokenError] which gives additional context to the error
/// with the provided message in [TokenError]
#[derive(Debug, Error)]
pub enum TokenErrorKind {
    /// Occurs when a escape sequence (within a character or a string) is malformed.
    #[error("Invalid character escape sequence.")]
    BadEscapeSequence,
    /// Occurs when a numerical literal doesn't follow the language specification, or is too large.
    #[error("Malformed numerical literal.")]
    MalformedNumericalLiteral,
    /// Occurs when a char is unexpected in the current context
    #[error("Encountered unexpected character {0}")]
    Unexpected(char),
    /// Occurs when the tokeniser expects a particular token next, but could not derive one.
    #[error("Expected token '{0}' here.")]
    Expected(TokenKind),
    /// Unclosed tree block
    #[error("Encountered unclosed delimiter '{}', consider adding a '{0}' after inner expression.", .0.left())]
    Unclosed(Delimiter),
}

/// This implementation exists since we can't use tuples that are un-named
/// with foreign module types.
pub struct TokenErrorWrapper(pub ModuleIdx, pub TokenError);

impl From<TokenErrorWrapper> for ParseError {
    fn from(TokenErrorWrapper(idx, err): TokenErrorWrapper) -> Self {
        ParseError::Parsing {
            message: err.to_string(),
            src: SourceLocation {
                location: err.location,
                module_index: idx,
            },
        }
    }
}

/// A GeneratorError represents possible errors that occur when transforming the token
/// stream into the AST.
#[derive(Debug, Constructor)]
pub struct AstGenError<'a> {
    /// The kind of the error.
    kind: AstGenErrorKind,
    /// Location of where the error references
    location: SourceLocation,
    /// An optional vector of tokens that are expected to circumvent the error.
    expected: Option<TokenKindVector<'a>>,
    /// An optional token in question that was received byt shouldn't of been
    received: Option<TokenKind>,
}

/// Enum representing the kind of statement where type arguments can be expected
/// to be present.
#[derive(Debug)]
pub enum TyArgumentKind {
    /// Type arguments at a struct definition.
    Struct,
    /// Type arguments at a enum definition.
    Enum,
}

/// Enum representation of the AST generation error variants.
#[derive(Debug)]
pub enum AstGenErrorKind {
    /// Expected keyword at current location
    Keyword,
    /// Generic error specifying an expected token atom.
    Expected,
    /// Expected the beginning of a body block.
    Block,
    /// Expected end of input or token stream here, but encountered tokens.
    EOF,
    /// Expecting a re-assignment operator at the specified location. Re-assignment operators
    /// are like normal operators, but they expect an 'equals' sign after the specified
    /// operator.
    ReAssignmentOp,
    /// Error representing expected type arguments. This error has two variants, it can
    /// either be 'struct' or 'enum' type arguments. The reason why there are two variants
    /// is to add additional information in the error message.
    TyArgument(TyArgumentKind),
    /// Expected statement.
    ExpectedStatement,
    /// Expected an expression.
    ExpectedExpression,
    /// Expected a '=>' at the current location. This error can occur in a number of places; including
    /// but not limited to: after type arguments, lambda definition, trait bound annotation, etc.
    ExpectedArrow,
    /// Specific error when expecting an arrow after the function definition
    ExpectedFnArrow,
    /// Expected a function body at the current location.
    ExpectedFnBody,
    /// Expected a type at the current location.
    ExpectedType,
    /// After a dot operator, the parser expects either a property access or an
    /// infix call which is an extended version of a property access.
    InfixCall,
    /// When the `import()` directive is used, the only argument should be a string path.
    /// @@Future: @@CompTime: This could likely change in the future.
    ImportPath,
    /// Expected an identifier after a name qualifier '::'.
    AccessName,
    /// If an imported module has errors, it should be reported
    ErroneousImport(ImportError),
}

/// This implementation exists since we can't use tuples that are un-named
/// with foreign module types.
pub struct GeneratorErrorWrapper<'a>(pub ModuleIdx, pub AstGenError<'a>);

impl std::fmt::Display for TyArgumentKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TyArgumentKind::Struct => write!(f, "struct"),
            TyArgumentKind::Enum => write!(f, "enumeration"),
        }
    }
}

/// Conversion implementation from an AST Generator Error into a Parser Error.
impl<'a> From<AstGenError<'a>> for ParseError {
    fn from(err: AstGenError) -> Self {
        let expected = err.expected;

        let mut base_message = match &err.kind {
            AstGenErrorKind::Keyword => {
                let keyword = err.received.unwrap();

                format!("Encountered an unexpected keyword '{}'", keyword)
            }
            AstGenErrorKind::Expected => match &err.received {
                Some(atom) => format!("Unexpectedly encountered '{}'", atom),
                None => "Unexpectedly reached the end of input".to_string(),
            },
            AstGenErrorKind::Block => {
                let base: String = "Expected block body, which begins with a '{'".into();

                match err.received {
                    Some(atom) => format!("{}, however received '{}'.", base, atom),
                    None => base,
                }
            }
            AstGenErrorKind::EOF => "Unexpectedly reached the end of input".to_string(),
            AstGenErrorKind::ReAssignmentOp => "Expected a re-assignment operator here".to_string(),
            AstGenErrorKind::TyArgument(ty) => {
                format!(
                    "Expected {} type arguments, or {} definition entries here which begin with a '{{'",
                    ty, ty
                )
            }
            AstGenErrorKind::ExpectedStatement => "Expected an statement here".to_string(),
            AstGenErrorKind::ExpectedExpression => "Expected an expression here".to_string(),
            AstGenErrorKind::ExpectedArrow => "Expected an arrow '=>' here".to_string(),
            AstGenErrorKind::ExpectedFnArrow => {
                "Expected an arrow '=>' after type arguments denoting a function type".to_string()
            }
            AstGenErrorKind::ExpectedFnBody => "Expected a function body here".to_string(),
            AstGenErrorKind::ExpectedType => "Expected a type annotation here".to_string(),
            AstGenErrorKind::InfixCall => {
                "Expected field name access or an infix function call".to_string()
            }
            AstGenErrorKind::ImportPath => {
                "Expected an import path which should be a string".to_string()
            }
            AstGenErrorKind::ErroneousImport(err) => err.to_string(),
            AstGenErrorKind::AccessName => {
                "Expected identifier after a name access qualifier '::'".to_string()
            }
        };

        // Block and expected format the error message in their own way, whereas all the
        // other error types follow a conformed order to formatting expected tokens
        if !matches!(&err.kind, AstGenErrorKind::Block) {
            if !matches!(&err.kind, AstGenErrorKind::Expected) {
                if let Some(atom) = err.received {
                    let atom_msg = format!(", however received a '{}'", atom);
                    base_message.push_str(&atom_msg);
                }
            }

            if let Some(expected) = expected {
                let expected_items_msg = format!(". Consider adding {}", expected);
                base_message.push_str(&expected_items_msg);
            } else {
                base_message.push('.');
            }
        }

        Self::Parsing {
            message: base_message,
            src: err.location,
        }
    }
}
