//! Hash Compiler lexer error data types.

use std::convert::Infallible;

use derive_more::Constructor;
use hash_reporting::{
    builder::ReportBuilder,
    diagnostic::Diagnostics,
    report::{Report, ReportCodeBlock, ReportElement, ReportKind},
};
use hash_source::location::SourceLocation;
use hash_token::{delimiter::Delimiter, TokenKind};
use thiserror::Error;

use crate::Lexer;

/// Utility type that wraps a [Result] and a [LexerError]
pub type LexerResult<T> = Result<T, LexerError>;

/// A [LexerError] represents a encountered error during tokenisation, which
/// includes an optional message with the error, the [LexerErrorKind] which
/// classifies the error, and a [SourceLocation] that represents where the
/// tokenisation error occurred.
#[derive(Debug, Constructor, Error)]
#[error("{kind}{}", .message.as_ref().map(|s| format!(". {s}")).unwrap_or_else(|| String::from("")))]
pub struct LexerError {
    message: Option<String>,
    kind: LexerErrorKind,
    location: SourceLocation,
}

/// A [LexerErrorKind] represents the kind of [LexerError] which gives
/// additional context to the error with the provided message in [LexerError]
#[derive(Debug, Error)]
pub enum LexerErrorKind {
    /// Occurs when a escape sequence (within a character or a string) is
    /// malformed.
    #[error("invalid character escape sequence")]
    BadEscapeSequence,
    /// Occurs when a numerical literal doesn't follow the language
    /// specification, or is too large.
    #[error("malformed numerical literal")]
    MalformedNumericalLit,
    /// Occurs when a float literal exponent has no proceeding digits.
    #[error("expected float exponent to have at least one digit")]
    MissingExponentDigits,
    /// Occurs when a numerical literal doesn't follow the language
    /// specification, or is too large.
    #[error("unclosed string literal")]
    UnclosedStringLit,
    /// Occurs when a character literal is comprised of more than one character
    #[error("invalid character literal `{0}`, character literals may only contain one codepoint")]
    InvalidCharacterLit(String),
    /// Occurs when a char is unexpected in the current context
    #[error("encountered unexpected character `{0}`")]
    Unexpected(char),
    /// Occurs when the tokeniser expects a particular token next, but could not
    /// derive one.
    #[error("expected token `{0}`")]
    Expected(TokenKind),
    /// Unclosed tree block
    #[error("encountered unclosed delimiter `{}`, add a `{0}` after the inner expression", .0.left())]
    Unclosed(Delimiter),
}

impl From<LexerError> for Report {
    fn from(err: LexerError) -> Self {
        let mut builder = ReportBuilder::new();

        builder
            .with_kind(ReportKind::Error)
            .with_message(err.to_string())
            .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(err.location, "here")));

        builder.build()
    }
}

/// Lexer error store, the lexer stores an internal store so that
/// it can implement [Diagnostics::DiagnosticsStore]
#[derive(Default)]
pub struct LexerDiagnostics {
    errors: Vec<LexerError>,
}

impl Diagnostics<LexerError, Infallible> for Lexer<'_> {
    type DiagnosticsStore = LexerDiagnostics;

    fn store(&self) -> &Self::DiagnosticsStore {
        &self.diagnostics
    }

    fn store_mut(&mut self) -> &mut Self::DiagnosticsStore {
        &mut self.diagnostics
    }

    /// Add an error into the store
    fn add_error(&mut self, error: LexerError) {
        self.store_mut().errors.push(error);
    }

    /// The lexer does not currently emit any warnings and so if this
    /// is called, it should panic.
    fn add_warning(&mut self, warning: Infallible) {
        match warning {}
    }

    fn has_errors(&self) -> bool {
        !self.store().errors.is_empty()
    }

    /// Lexer never emits any warnings so this always false
    fn has_warnings(&self) -> bool {
        false
    }

    fn into_reports(self) -> Vec<Report> {
        self.diagnostics.errors.into_iter().map(|err| err.into()).collect()
    }

    fn into_diagnostics(self) -> (Vec<LexerError>, Vec<Infallible>) {
        (self.diagnostics.errors, vec![])
    }

    fn merge(&mut self, other: impl Diagnostics<LexerError, Infallible>) {
        let (errors, _) = other.into_diagnostics();
        self.diagnostics.errors.extend(errors)
    }
}
