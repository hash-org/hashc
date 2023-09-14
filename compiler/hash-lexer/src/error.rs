//! Hash Compiler lexer error data types.

use std::{cell::Cell, fmt::Display};

use hash_reporting::{
    diagnostic::{DiagnosticStore, HasDiagnosticsMut},
    report::{Report, ReportElement, ReportNote, ReportNoteKind},
    reporter::{Reporter, Reports},
};
use hash_source::{identifier::Identifier, location::Span};
use hash_token::{delimiter::Delimiter, Base, TokenKind};

use crate::Lexer;

/// Auxiliary data type to provide more information about the
/// numerical literal kind that was encountered. This is used
/// to give more accurate information about if the numerical
/// literal was a `number` or a `float`. The reason why it
/// is a number is because it still not clear whether this
/// is meant to be an integer or a float.
#[derive(Debug, Clone, Copy)]
pub enum NumericLitKind {
    /// Unclear, could be a `integer` or `float`
    Integer,
    /// Known to be a `float`
    Float,
}

impl Display for NumericLitKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NumericLitKind::Integer => write!(f, "integer"),
            NumericLitKind::Float => write!(f, "float"),
        }
    }
}

/// Utility type that wraps a [Result] and a [LexerError]
pub type LexerResult<T> = Result<T, LexerError>;

/// A [LexerError] represents a encountered error during tokenisation, which
/// includes an optional message with the error, the [LexerErrorKind] which
/// classifies the error, and a [Span] that represents where the
/// tokenisation error occurred.
#[derive(Debug)]
pub struct LexerError {
    /// The kind of the error.
    pub(crate) kind: LexerErrorKind,

    /// Additional information about the error, if any.
    pub(crate) message: Option<String>,

    /// The location of the error, this includes the span and the id of the
    /// source.
    pub(crate) location: Span,
}

/// A [LexerErrorKind] represents the kind of [LexerError] which gives
/// additional context to the error with the provided message in [LexerError]
#[derive(Debug)]
pub enum LexerErrorKind {
    /// Occurs when a escape sequence (within a character or a string) is
    /// malformed.
    BadEscapeSequence,

    /// Occurs when a numerical literal doesn't follow the language
    /// specification, or is too large.
    MalformedNumericalLit,

    /// Occurs when a float literal exponent has no proceeding digits.
    MissingExponentDigits,

    /// When an integer is specified, but no valid digits follow.
    MissingDigits,

    /// Occurs when a string literal is unclosed.
    UnclosedStringLit,

    /// Occurs when a character literal is comprised of more than one character
    InvalidCharacterLit(String),

    /// Occurs when a char is unexpected in the current context
    Unexpected(char),

    /// Occurs when the tokeniser expects a particular token next, but could not
    /// derive one.
    Expected(TokenKind),

    /// Unclosed tree block
    Unclosed(Delimiter),

    /// Unsupported radix featured on a float literal...
    UnsupportedFloatBaseLiteral(Base),

    /// Invalid literal ascription for either `float` or `integer`
    InvalidLitSuffix(NumericLitKind, Identifier),
}

impl From<LexerError> for Reports {
    fn from(err: LexerError) -> Self {
        let mut reporter = Reporter::new();

        // We can have multiple notes describing what could be done about the error.
        let mut help_notes = vec![];

        let mut message = match err.kind {
            LexerErrorKind::BadEscapeSequence => "invalid character escape sequence".to_string(),
            LexerErrorKind::MalformedNumericalLit => "malformed numerical literal".to_string(),
            LexerErrorKind::MissingExponentDigits => "float exponent to have at least one digit".to_string(),
            LexerErrorKind::MissingDigits => "missing digits after integer base prefix".to_string(),
            LexerErrorKind::UnclosedStringLit => "unclosed string literal".to_string(),
            LexerErrorKind::InvalidCharacterLit(char) => format!("invalid character literal `{char}`, character literals may only contain one codepoint"),
            LexerErrorKind::Unexpected(char) => format!("encountered unexpected character `{char}`"),
            LexerErrorKind::Expected(token) => format!("expected token `{token}`"),
            LexerErrorKind::Unclosed(delim) => format!("encountered unclosed delimiter `{}`, add a `{delim}` after the inner expression", delim.left()),
            LexerErrorKind::UnsupportedFloatBaseLiteral(base) => format!("{base} float literal is not supported"),
            LexerErrorKind::InvalidLitSuffix(kind, suffix) => {
                    let suffix_note = match kind {
                        NumericLitKind::Integer => format!("{kind} suffix must be `u32`, `i64`, etc"),
                        NumericLitKind::Float => format!("{kind} suffix must be `f32` or `f64`"),
                    };

                    // push a note about what kind of suffix is expected
                    help_notes
                        .push(ReportElement::Note(ReportNote::new(ReportNoteKind::Info, suffix_note)));

                    format!("invalid suffix `{suffix}` for {kind} literal")
                }
        };

        if let Some(additional_info) = err.message {
            message.push_str(&format!(". {additional_info}"));
        }

        reporter.error().title(message).add_labelled_span(err.location, "here");

        reporter.into_reports()
    }
}

/// Lexer error store, the lexer stores an internal store so that
/// it can implement [Diagnostics::DiagnosticsStore]
#[derive(Default)]
pub struct LexerDiagnostics {
    /// Inner stored diagnostics from the lexer.
    store: DiagnosticStore<LexerError, ()>,

    /// Whether the [Lexer] encountered a fatal error and
    /// must abort on the next token advance
    pub(crate) has_fatal_error: Cell<bool>,
}

impl HasDiagnosticsMut for Lexer<'_> {
    type Diagnostics = DiagnosticStore<LexerError, ()>;

    fn diagnostics(&mut self) -> &mut Self::Diagnostics {
        &mut self.diagnostics.store
    }
}

impl Lexer<'_> {
    pub fn into_reports(&mut self) -> Vec<Report> {
        self.diagnostics.store.errors.drain(..).flat_map(Reports::from).collect()
    }
}
