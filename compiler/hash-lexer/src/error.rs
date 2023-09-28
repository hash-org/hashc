//! Hash Compiler lexer error data types.

use std::{cell::Cell, fmt::Display};

use hash_reporting::{
    diagnostic::{DiagnosticStore, HasDiagnosticsMut},
    report::{help, info, Report},
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

    /// The location of the error, this includes the span and the id of the
    /// source.
    pub(crate) location: Span,
}

/// A [LexerErrorKind] represents the kind of [LexerError] which gives
/// additional context to the error with the provided message in [LexerError]
#[derive(Debug)]
pub enum LexerErrorKind {
    /// Occurs when a numerical literal doesn't follow the language
    /// specification, or is too large.
    MalformedNumericalLit,

    /// Occurs when a float literal exponent has no proceeding digits.
    MissingExponentDigits,

    /// When an integer is specified, but no valid digits follow.
    MissingDigits,

    /// Occurs when a string literal is unclosed.
    UnclosedStringLit,

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

    /// Encountered a invalid float exponent.
    InvalidFloatExponent,

    /// Unclosed character literal, e.g.
    /// ```
    /// 'a
    /// ```
    UnclosedCharLit,

    /// When an empty character literal is specified, e.g.
    /// ```
    /// ''
    /// ```
    EmptyCharLit,

    /// Occurs when a escape sequence (within a character or a string) is
    /// not a valid escape sequence, e.g.
    /// ```
    /// '\z'
    /// ```
    ///
    /// The error contains the encountered invalid character.
    UnknownEscapeSequence(char),

    /// When a character literal has multiple code points, e.g.
    /// ```
    /// 'ab'
    /// ```
    MultipleCharCodePoints,

    /// Unclosed unicode literal, when a unicode character literal
    /// is missing the closing brace, e.g.
    /// ```
    /// '\u{1F600'
    /// ```
    UnclosedUnicodeLit,

    /// When a unicode literal begins with `u`, but doesn't continue
    /// with `{`, e.g.
    /// ```
    /// '\u1F600'
    /// ```
    MalformedUnicodeLit,

    /// When a unicode literal has invalid digits, e.g.
    /// ```
    /// '\u{1F6G00}'
    /// ```
    ///
    /// The error contains the encountered invalid character.
    InvalidUnicodeEscape(char),

    /// When a unicode literal is too long, e.g.
    /// ```
    /// '\u{1F600000000000}`
    /// ```
    UnicodeLitTooLong,

    /// When an ASCII escape sequence is too short, e.g.
    /// ```
    /// '\x'
    /// ```
    NumericEscapeSequenceTooShort,

    /// When an ASCII Escape is too large, e.g.
    /// ```
    /// '\x8f'
    /// ```
    ///
    /// The maximum valid ASCII codepoint is `\x7f`.
    NumericEscapeSequenceTooLarge,

    /// When an ASCII escape sequence has invalid digits, e.g.
    /// ```
    /// '\xMG'
    /// ```
    ///
    /// The error contains the encountered invalid character.
    InvalidNumericEscapeSequence(char),

    /// When a unicode literal is too large, e.g.
    /// ```
    /// '\u{FFFFFF}'
    /// ```
    ///
    /// This exceeds the maximum valid unicode codepoint of `10FFFF`.
    UnicodeLitTooLarge,

    /// When a unicode codepoint is present within a byte literal, e.g.
    /// ```
    /// b'\u{1F600}'
    /// ```
    UnicodeInByteLit,
}

impl From<LexerError> for Reports {
    fn from(err: LexerError) -> Self {
        let mut reporter = Reporter::new();

        let mut span_label = None;
        let mut help_notes = vec![];

        let message = match err.kind {
            LexerErrorKind::UnknownEscapeSequence(ch) => {
                format!("unrecognised character escape sequence `{ch}`")
            }
            LexerErrorKind::MalformedNumericalLit => "malformed numerical literal".to_string(),
            LexerErrorKind::MissingExponentDigits => {
                "float exponent to have at least one digit".to_string()
            }
            LexerErrorKind::MissingDigits => "missing digits after integer base prefix".to_string(),
            LexerErrorKind::UnclosedStringLit => "unclosed string literal".to_string(),
            LexerErrorKind::Unexpected(char) => {
                format!("encountered unexpected character `{char}`")
            }
            LexerErrorKind::Expected(token) => format!("expected token `{token}`"),
            LexerErrorKind::Unclosed(delim) => format!(
                "encountered unclosed delimiter `{}`, add a `{}` after the inner expression",
                delim.left(),
                delim.right()
            ),
            LexerErrorKind::UnsupportedFloatBaseLiteral(base) => {
                format!("{base} float literal is not supported")
            }
            LexerErrorKind::InvalidLitSuffix(kind, suffix) => {
                let suffix_note = match kind {
                    NumericLitKind::Integer => "suffix must be `u32`, `i64`, etc",
                    NumericLitKind::Float => "suffix must be `f32` or `f64`",
                };

                // push a note about what kind of suffix is expected
                help_notes.push(info!("{kind} {suffix_note}"));

                format!("invalid suffix `{suffix}` for {kind} literal")
            }
            LexerErrorKind::InvalidFloatExponent => {
                "float literal has an invalid exponent".to_string()
            }
            LexerErrorKind::UnclosedCharLit => {
                span_label = Some("expected `'` here".to_string());
                "unclosed character literal".to_string()
            }
            LexerErrorKind::EmptyCharLit => {
                span_label = Some("expected a character literal here".to_string());
                "empty character literal".to_string()
            }
            LexerErrorKind::MalformedUnicodeLit => {
                span_label = Some("expected `{` after a `\\u` escape sequence".to_string());
                "invalid unicode escape sequence".to_string()
            }
            LexerErrorKind::UnclosedUnicodeLit => {
                // push a note about what kind of suffix is expected
                span_label = Some("expected `}` here".to_string());
                "unclosed unicode escape sequence".to_string()
            }
            LexerErrorKind::MultipleCharCodePoints => {
                help_notes
                    .push(help!("{}", "if you meant to write a string literal, use `\"` instead"));
                "character literals may only contain one codepoint".to_string()
            }
            LexerErrorKind::InvalidUnicodeEscape(ch) => {
                help_notes
                    .push(info!("{}", "unicode literals may only contain hexadecimal digits"));
                format!("invalid character in unicode escape sequence `{ch}`")
            }
            LexerErrorKind::UnicodeLitTooLong => {
                span_label = Some(
                    "unicode literals may only contain up to 6 hexadecimal digits".to_string(),
                );
                "overlong unicode escape sequence".to_string()
            }
            LexerErrorKind::UnicodeLitTooLarge => {
                span_label = Some("invalid escape".to_string());
                help_notes.push(info!("{}", "unicode escape must be at most 10FFFF"));
                "invalid unicode character escape".to_string()
            }
            LexerErrorKind::UnicodeInByteLit => {
                span_label = Some("unicode escape in byte literal".to_string());
                help_notes.push(help!("{}", "unicode escape sequences cannot be used as a byte"));
                "unicode escape in byte literal".to_string()
            }
            LexerErrorKind::NumericEscapeSequenceTooShort => {
                "numeric escape sequence is too short".to_string()
            }
            LexerErrorKind::NumericEscapeSequenceTooLarge => {
                span_label = Some("must be a character in the range \\x00..\\x7F".to_string());
                "out of range hex escape".to_string()
            }
            LexerErrorKind::InvalidNumericEscapeSequence(ch) => {
                help_notes.push(info!(
                    "{}",
                    "numeric escape sequences may only contain hexadecimal digits"
                ));
                span_label = Some(format!("`{ch}` is not valid here"));
                format!("invalid character in numeric escape sequence `{ch}`")
            }
        };

        let report = reporter
            .error()
            .title(message)
            .add_labelled_span(err.location, span_label.unwrap_or("here".to_string()));

        // Add any of the additionally generated notes.
        for note in help_notes {
            report.add_element(note);
        }

        reporter.into_reports()
    }
}

/// Lexer error store, the lexer stores an internal store so that
/// it can implement [Diagnostics::DiagnosticsStore]
#[derive(Default)]
pub struct LexerDiagnostics {
    /// Inner stored diagnostics from the lexer.
    pub store: DiagnosticStore<LexerError, ()>,

    /// Whether the [Lexer] encountered a fatal error and
    /// must abort on the next token advance
    pub(crate) has_fatal_error: Cell<bool>,
}

impl LexerDiagnostics {
    /// Check if the lexer has encountered an error.
    pub fn has_errors(&self) -> bool {
        self.has_fatal_error.get() || !self.store.errors.is_empty()
    }

    /// Convert all of the collected [LexerDiagnostics] into [Report]s.
    pub fn into_reports(&mut self) -> Vec<Report> {
        self.store.errors.drain(..).flat_map(Reports::from).collect()
    }
}

impl HasDiagnosticsMut for Lexer<'_> {
    type Diagnostics = DiagnosticStore<LexerError, ()>;

    fn diagnostics(&mut self) -> &mut Self::Diagnostics {
        &mut self.diagnostics.store
    }
}
