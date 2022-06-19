//! Hash Compiler parser error data types.

use derive_more::Constructor;
use hash_source::{location::Span, SourceId};
use hash_token::{delimiter::Delimiter, TokenKind};
use thiserror::Error;

/// Utility type that wraps a [Result] and a [LexerError]
pub type LexerResult<T> = Result<T, LexerError>;

/// A [LexerError] represents a encountered error during tokenisation, which includes an optional message
/// with the error, the [LexerErrorKind] which classifies the error, and a [Span] that represents
/// where the tokenisation error occurred.
#[derive(Debug, Constructor, Error)]
#[error("{kind}{}", .message.as_ref().map(|s| format!(". {s}")).unwrap_or_else(|| String::from("")))]
pub struct LexerError {
    pub(crate) message: Option<String>,
    kind: LexerErrorKind,
    pub span: Span,
}

/// This implementation exists since we can't use tuples that are un-named
/// with foreign module types.
pub struct LexerErrorWrapper(pub SourceId, pub LexerError);

/// A [LexerErrorKind] represents the kind of [LexerError] which gives additional context to the error
/// with the provided message in [LexerError]
#[derive(Debug, Error)]
pub enum LexerErrorKind {
    /// Occurs when a escape sequence (within a character or a string) is malformed.
    #[error("Invalid character escape sequence")]
    BadEscapeSequence,
    /// Occurs when a numerical literal doesn't follow the language specification, or is too large.
    #[error("Malformed numerical literal")]
    MalformedNumericalLiteral,
    /// Occurs when a float literal exponent has no proceeding digits.
    #[error("Expected float exponent to have at least one digit")]
    MissingExponentDigits,
    /// Occurs when a numerical literal doesn't follow the language specification, or is too large.
    #[error("Unclosed string literal")]
    UnclosedStringLiteral,
    /// Occurs when a character literal is comprised of more than one character
    #[error("Invalid character literal `{0}`, character literals may only contain one codepoint")]
    InvalidCharacterLiteral(String),
    /// Occurs when a char is unexpected in the current context
    #[error("Encountered unexpected character `{0}`")]
    Unexpected(char),
    /// Occurs when the tokeniser expects a particular token next, but could not derive one.
    #[error("Expected token `{0}`")]
    Expected(TokenKind),
    /// Unclosed tree block
    #[error("Encountered unclosed delimiter `{}`, add a `{0}` after the inner expression", .0.left())]
    Unclosed(Delimiter),
}

// For now, we don't use the reporting capabilities within the lexer and just let the
// `hash-parser` crate handle the reporting. This is partially due to the fact that
// the current infrastructure within the compiler will lex and parse at the same time
// within the thread pool. Ideally, instead of passing `<Lexer|Parser>Error` around, we
// could just use the `Report` type which is agnostic and can also be sent as messages
// around the sub-systems.

// impl LexerError {
//     pub fn create_report(&self, source_id: SourceId) -> Report {
//         let mut builder = ReportBuilder::new();

//         builder
//             .with_kind(ReportKind::Error)
//             .with_message("Failed to parse")
//             .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
//                 SourceLocation {
//                     span: self.span,
//                     source_id,
//                 },
//                 "here",
//             )))
//             .add_element(ReportElement::Note(ReportNote::new(
//                 ReportNoteKind::Note,
//                 self.to_string(),
//             )));

//         builder.build().unwrap()
//     }
// }

// impl From<LexerErrorWrapper> for Report {
//     fn from(LexerErrorWrapper(source_id, err): LexerErrorWrapper) -> Self {
//         err.create_report(source_id)
//     }
// }
