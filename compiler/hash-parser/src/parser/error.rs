//! Hash compiler parser error data types.
//!
//! All rights reserved 2022 (c) The Hash Language authors

use std::io;

use derive_more::Constructor;
use hash_lexer::error::LexerErrorWrapper;
use hash_pipeline::fs::ImportError;
use hash_reporting::reporting::{
    Report, ReportBuilder, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind,
};
use hash_source::location::SourceLocation;
use hash_token::{TokenKind, TokenKindVector};
use hash_utils::printing::SequenceDisplay;

/// A [AstGenError] represents possible errors that occur when transforming the token
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
    /// Expected an identifier here.
    ExpectedIdentifier,
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

                format!(
                    "Encountered an unexpected keyword {}",
                    keyword.as_error_string()
                )
            }
            AstGenErrorKind::Expected => match &err.received {
                Some(kind) => format!("Unexpectedly encountered {}", kind.as_error_string()),
                None => "Unexpectedly reached the end of input".to_string(),
            },
            AstGenErrorKind::Block => {
                let base: String = "Expected block body, which begins with a '{'".into();

                match err.received {
                    Some(kind) => {
                        format!("{}, however received '{}'.", base, kind.as_error_string())
                    }
                    None => base,
                }
            }
            AstGenErrorKind::EOF => "Unexpectedly reached the end of input".to_string(),
            AstGenErrorKind::ReAssignmentOp => "Expected a re-assignment operator".to_string(),
            AstGenErrorKind::TyArgument(ty) => {
                format!(
                    "Expected {} type arguments, or {} definition entries here which begin with a '{{'",
                    ty, ty
                )
            }
            AstGenErrorKind::ExpectedStatement => "Expected an statement".to_string(),
            AstGenErrorKind::ExpectedExpression => "Expected an expression".to_string(),
            AstGenErrorKind::ExpectedIdentifier => "Expected an identifier".to_string(),
            AstGenErrorKind::ExpectedArrow => "Expected an arrow '=>' ".to_string(),
            AstGenErrorKind::ExpectedFnArrow => {
                "Expected an arrow '->' after type arguments denoting a function type".to_string()
            }
            AstGenErrorKind::ExpectedFnBody => "Expected a function body".to_string(),
            AstGenErrorKind::ExpectedType => "Expected a type annotation".to_string(),
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
                if let Some(kind) = err.received {
                    let atom_msg = format!(", however received {}", kind.as_error_string());
                    base_message.push_str(&atom_msg);
                }
            }

            // If the generated error has suggested tokens that aren't empty.
            if let Some(expected) = expected {
                if expected.is_empty() {
                    base_message.push('.');
                } else {
                    let slice_display = SequenceDisplay(expected.into_inner().into_slice());
                    let expected_items_msg = format!(". Consider adding {}", slice_display);
                    base_message.push_str(&expected_items_msg);
                }
            } else {
                base_message.push('.');
            }
        }

        Self::Parsing {
            message: base_message,
            src: Some(err.location),
        }
    }
}

/// Hash ParseError enum representing the variants of possible errors.
#[derive(Debug)]
pub enum ParseError {
    Import(ImportError),
    IO(io::Error),
    Parsing {
        message: String,
        src: Option<SourceLocation>,
    },
}

impl From<io::Error> for ParseError {
    fn from(err: io::Error) -> Self {
        Self::IO(err)
    }
}

impl From<ParseError> for Report {
    fn from(err: ParseError) -> Self {
        err.create_report()
    }
}

impl ParseError {
    pub fn create_report(self) -> Report {
        let mut builder = ReportBuilder::new();
        builder
            .with_kind(ReportKind::Error)
            .with_message("Failed to parse");

        match self {
            ParseError::Import(import_error) => return import_error.create_report(),
            ParseError::Parsing {
                message,
                src: Some(src),
            } => {
                builder
                    .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(src, "here")))
                    .add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Note,
                        message,
                    )));
            }
            // When we don't have a source for the error, just add a note
            ParseError::Parsing { message, src: None } => {
                builder.with_message(message);
            }
            ParseError::IO(inner) => {
                // @@ErrorReporting: we might want to show a bit more info here.
                builder.with_message(inner.to_string());
            }
        };

        // @@ErrorReporting: we might want to properly handle incomplete reports?
        builder.build().unwrap()
    }
}

pub type ParseResult<T> = Result<T, ParseError>;

impl From<LexerErrorWrapper> for ParseError {
    fn from(LexerErrorWrapper(source_id, err): LexerErrorWrapper) -> Self {
        ParseError::Parsing {
            message: err.to_string(),
            src: Some(SourceLocation {
                location: err.location,
                source_id,
            }),
        }
    }
}
