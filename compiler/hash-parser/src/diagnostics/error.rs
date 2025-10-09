//! Hash Compiler parser error utilities.
use derive_more::Constructor;
use hash_ast::{ast::TyParamOrigin, origin::PatOrigin};
use hash_pipeline::fs::ImportError;
use hash_reporting::{
    report::help,
    reporter::{Reporter, Reports},
};
use hash_source::{identifier::Identifier, location::Span};
use hash_token::TokenKind;

use super::expected::ExpectedItem;

/// Utility wrapper type for [ParseError] in [Result]
pub type ParseResult<T> = Result<T, ParseError>;

/// A [ParseError] represents possible errors that occur when transforming the
/// token stream into the AST.
#[derive(Debug, Clone, Constructor)]
pub struct ParseError {
    /// The kind of the error.
    kind: ParseErrorKind,

    /// Location of where the error references
    location: Span,

    /// An optional vector of tokens that are expected to circumvent the error.
    expected: ExpectedItem,

    /// An optional token in question that was received byt shouldn't of been
    received: Option<TokenKind>,
}

/// Enum representation of the AST generation error variants.
#[derive(Debug, Clone)]
pub enum ParseErrorKind {
    /// Generic error specifying an expected token atom.
    UnExpected,

    /// Error representing expected type arguments. This error has two variants,
    /// it can either be 'struct' or 'enum' type arguments. The reason why
    /// there are two variants is to add additional information in the error
    /// message.
    TyDef(TyParamOrigin),

    /// Expected the beginning of a body block.
    ExpectedBlock,

    /// Expected a name here.
    ExpectedName,

    /// Expected a macro invocation, either being a name identifier or a
    /// bracketed list of macro invocations.
    ExpectedMacroInvocation,

    /// Expected an expression.
    ExpectedExpr,

    /// Expected a function body at the current location.
    ExpectedFnBody,

    /// Expected a type at the current location.
    ExpectedTy,

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

    /// If an imported module has errors, it should be reported
    ErroneousImport(ImportError),

    /// Malformed spread pattern (if for any reason there is a problem with
    /// parsing the spread operator)
    MalformedSpreadPat(u8),

    /// When a spread pattern is featured in a compound pattern which
    /// does not accept spread patterns.
    DisallowedSpreadPat {
        /// Where the use of the pattern originated from.
        origin: PatOrigin,
    },

    /// When multiple spread patterns `...` are present within a list, tuple
    /// or constructor pattern.
    MultipleSpreadPats {
        /// Where the use of the pattern originated from.
        origin: PatOrigin,
    },

    /// When a suffix is not allowed on a numeric literal, specifically
    /// when it used as a property access field.
    DisallowedSuffix(Identifier),

    /// When a property access is invalid: currently emitted when:
    ///
    /// - numeric fields attempt to access a field which is larger than [usize].
    InvalidPropertyAccess,

    /// When an attempt is made to write an expression which would evaluate to a
    /// negative literal, i.e. `- 1`, `- /* boo! */ 2`, etc.
    UnsupportedExprInPat { value: String },
}

/// Conversion implementation from an AST Generator Error into a Parser Error.
impl From<ParseError> for Reports {
    fn from(err: ParseError) -> Self {
        let expected = err.expected;

        // Default label used when marking where the error occurred
        let mut span_label = "".to_string();

        // We can have multiple notes describing what could be done about the error.
        let mut help_notes = vec![];

        let mut base_message = match &err.kind {
            ParseErrorKind::UnExpected => match &err.received {
                Some(kind) => format!("unexpectedly encountered {}", kind.as_error_string()),
                None => "unexpectedly reached the end of input".to_string(),
            },
            ParseErrorKind::TyDef(ty) => {
                format!(
                    "expected {} definition entries here which begin with a `<` or `(`",
                    ty.name()
                )
            }
            ParseErrorKind::ExpectedBlock => {
                "expected block body, which begins with a `{`".to_string()
            }
            ParseErrorKind::ExpectedExpr => "expected an expression".to_string(),
            ParseErrorKind::ExpectedName => "expected a name here".to_string(),
            ParseErrorKind::ExpectedMacroInvocation => "expected a macro invocation".to_string(),
            ParseErrorKind::ExpectedFnBody => "expected a function body".to_string(),
            ParseErrorKind::ExpectedTy => "expected a type annotation".to_string(),
            ParseErrorKind::ExpectedPropertyAccess => {
                "expected field name access or a method call".to_string()
            }
            ParseErrorKind::ExpectedPat => "expected pattern".to_string(),
            ParseErrorKind::ImportPath => {
                "expected an import path which should be a string".to_string()
            }
            ParseErrorKind::ErroneousImport(err) => err.to_string(),
            ParseErrorKind::MalformedSpreadPat(dots) => {
                format!(
                    "malformed spread pattern, expected {dots} more `.` to complete the pattern"
                )
            }
            ParseErrorKind::DisallowedSpreadPat { origin } => {
                span_label = "cannot specify a `...` here".to_string();

                format!("spread patterns `...` cannot be used in a {origin} pattern",)
            }
            ParseErrorKind::DisallowedSuffix(suffix) => {
                span_label = format!("disallowed suffix `{suffix}`");

                "suffixes on property access fields are disallowed".to_string()
            }
            ParseErrorKind::InvalidPropertyAccess => "invalid property access".to_string(),
            ParseErrorKind::MultipleSpreadPats { origin } => {
                span_label = "cannot specify another spread pattern here".to_string();

                format!("spread patterns `...` can only be used once in a {origin} pattern")
            }
            ParseErrorKind::UnsupportedExprInPat { value } => {
                help_notes.push(help!("consider writing the literal as `-{}`", *value));

                "negative numerical literals must be written as a single numerical value"
                    .to_string()
            }
        };

        // `AstGenErrorKind::Expected` format the error message in their own way,
        // whereas all the other error types follow a conformed order to
        // formatting expected tokens
        if !matches!(&err.kind, ParseErrorKind::UnExpected)
            && let Some(kind) = err.received
        {
            let atom_msg = format!(", however received {}", kind.as_error_string());
            base_message.push_str(&atom_msg);
        }

        // If the generated error has suggested tokens that aren't empty.
        if !expected.is_empty() {
            help_notes.push(help!("expected {expected}"));
        }

        // Now actually build the report
        let mut reporter = Reporter::new();
        let report = reporter.error();
        report.title(base_message).add_labelled_span(err.location, span_label);

        // Add the `help` messages to the report
        for note in help_notes {
            report.add_element(note);
        }

        reporter.into_reports()
    }
}
