//! Hash Compiler parser error utilities.
use std::io;

use derive_more::Constructor;
use hash_lexer::error::LexerErrorWrapper;
use hash_pipeline::fs::ImportError;
use hash_reporting::{
    builder::ReportBuilder,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind, ReportNote, ReportNoteKind},
};
use hash_source::location::SourceLocation;
use hash_token::{TokenKind, TokenKindVector};
use hash_utils::printing::SequenceDisplay;

/// A [AstGenError] represents possible errors that occur when transforming the
/// token stream into the AST.
#[derive(Debug, Constructor)]
pub struct AstGenError {
    /// The kind of the error.
    kind: AstGenErrorKind,
    /// Location of where the error references
    span: SourceLocation,
    /// An optional vector of tokens that are expected to circumvent the error.
    expected: Option<TokenKindVector>,
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
    /// Expecting a re-assignment operator at the specified location.
    /// Re-assignment operators are like normal operators, but they expect
    /// an 'equals' sign after the specified operator.
    ReAssignmentOp,
    /// Error representing expected type arguments. This error has two variants,
    /// it can either be 'struct' or 'enum' type arguments. The reason why
    /// there are two variants is to add additional information in the error
    /// message.
    TypeDefinition(TyArgumentKind),
    /// Expected a name here.
    ExpectedName,
    /// Expected a binary operator that ties two expressions together to create
    /// a binary expression.
    ExpectedOperator,
    /// Expected an expression.
    ExpectedExpr,
    /// Expected a '=>' at the current location. This error can occur in a
    /// number of places; including but not limited to: after type
    /// arguments, lambda definition, trait bound annotation, etc.
    ExpectedArrow,
    /// Specific error when expecting an arrow after the function definition
    ExpectedFnArrow,
    /// Expected a function body at the current location.
    ExpectedFnBody,
    /// Expected a type at the current location.
    ExpectedType,
    /// Expected an expression after a type annotation within named tuples
    ExpectedValueAfterTyAnnotation,
    /// After a dot operator, the parser expects either a property access or an
    /// infix-like method call which is an extended version of a property
    /// access.
    ExpectedPropertyAccess,
    /// Expected a pattern at this location
    ExpectedPat,
    /// When the `import()` directive is used, the only argument should be a
    /// string path. @@Future: @@CompTime: This could likely change in the
    /// future.
    ImportPath,
    /// Expected an identifier after a name qualifier '::'.
    Namespace,
    /// If an imported module has errors, it should be reported
    ErroneousImport(ImportError),
    /// Malformed spread pattern (if for any reason there is a problem with
    /// parsing the spread operator)
    MalformedSpreadPattern(u8),
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
impl From<AstGenError> for ParseError {
    fn from(err: AstGenError) -> Self {
        let expected = err.expected;

        let mut base_message = match &err.kind {
            AstGenErrorKind::Keyword => {
                let keyword = err.received.unwrap();

                format!("encountered an unexpected keyword {}", keyword.as_error_string())
            }
            AstGenErrorKind::Expected => match &err.received {
                Some(kind) => format!("unexpectedly encountered {}", kind.as_error_string()),
                None => "unexpectedly reached the end of input".to_string(),
            },
            AstGenErrorKind::Block => {
                let base: String = "expected block body, which begins with a '{'".into();

                match err.received {
                    Some(kind) => {
                        format!("{}, however received '{}'.", base, kind.as_error_string())
                    }
                    None => base,
                }
            }
            AstGenErrorKind::EOF => "unexpectedly reached the end of input".to_string(),
            AstGenErrorKind::ReAssignmentOp => "Expected a re-assignment operator".to_string(),
            AstGenErrorKind::TypeDefinition(ty) => {
                format!("expected {} definition entries here which begin with a '('", ty)
            }
            AstGenErrorKind::ExpectedValueAfterTyAnnotation => {
                "expected value assignment after type annotation within named tuple".to_string()
            }
            AstGenErrorKind::ExpectedOperator => "expected an operator".to_string(),
            AstGenErrorKind::ExpectedExpr => "expected an expression".to_string(),
            AstGenErrorKind::ExpectedName => "expected a name here".to_string(),
            AstGenErrorKind::ExpectedArrow => "expected an arrow '=>' ".to_string(),
            AstGenErrorKind::ExpectedFnArrow => {
                "expected an arrow '->' after type arguments denoting a function type".to_string()
            }
            AstGenErrorKind::ExpectedFnBody => "expected a function body".to_string(),
            AstGenErrorKind::ExpectedType => "expected a type annotation".to_string(),
            AstGenErrorKind::ExpectedPropertyAccess => {
                "expected field name access or a method call".to_string()
            }
            AstGenErrorKind::ExpectedPat => "expected pattern".to_string(),
            AstGenErrorKind::ImportPath => {
                "expected an import path which should be a string".to_string()
            }
            AstGenErrorKind::ErroneousImport(err) => err.to_string(),
            AstGenErrorKind::Namespace => {
                "expected identifier after a name access qualifier '::'".to_string()
            }
            AstGenErrorKind::MalformedSpreadPattern(dots) => {
                format!(
                    "malformed spread pattern, expected {dots} more `.` to complete the pattern"
                )
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

            base_message.push('.');
        }

        // If the generated error has suggested tokens that aren't empty.
        let help = expected.map(|tokens| {
            format!("consider adding {}", SequenceDisplay::either(tokens.into_inner().as_slice()))
        });

        Self::Parsing { message: base_message, location: Some(err.span), help }
    }
}

/// Hash ParseError enum representing the variants of possible errors.
#[derive(Debug)]
pub enum ParseError {
    Import(ImportError),
    IO(io::Error),
    Parsing {
        /// The generated error message.
        message: String,
        /// Location of the parsing error, it is optional since sometimes it
        /// isn't yet possible to get the span of the error.
        location: Option<SourceLocation>,
        /// An optional help message that is generated from the error.
        help: Option<String>,
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
        builder.with_kind(ReportKind::Error).with_message("failed to parse");

        match self {
            ParseError::Import(import_error) => return import_error.create_report(),
            ParseError::Parsing { message, location, help } => {
                if let Some(location) = location {
                    builder
                        .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
                            location, "here",
                        )))
                        .add_element(ReportElement::Note(ReportNote::new(
                            ReportNoteKind::Note,
                            message,
                        )));
                } else {
                    // When we don't have a source for the error, just add a note
                    builder.with_message(message);
                }

                // Add the `help` message as a separate note
                if let Some(message) = help {
                    builder.add_element(ReportElement::Note(ReportNote::new(
                        ReportNoteKind::Help,
                        message,
                    )));
                }
            }
            ParseError::IO(inner) => {
                // @@ErrorReporting: we might want to show a bit more info here.
                builder.with_message(inner.to_string());
            }
        };

        builder.build()
    }
}

impl From<LexerErrorWrapper> for ParseError {
    /// Implementation to convert a [`hash_lexer::error::LexerError`] with the
    /// combination of a [`hash_source::SourceId`] into a [ParseError]. This
    /// is used in order to interface with the lexer within the parsing
    /// stage.
    ///
    /// @@Future: In the future, there is a hope that we don't
    /// need to convert between various error kinds in crates and they can just
    /// be passed around as reports which are pipeline stage agnostic.
    fn from(LexerErrorWrapper(source_id, err): LexerErrorWrapper) -> Self {
        ParseError::Parsing {
            message: err.to_string(),
            location: Some(SourceLocation { span: err.span, source_id }),
            help: None,
        }
    }
}
