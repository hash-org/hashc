//! Hash diagnostic report data structures.
use std::{cell::Cell, fmt};

use crate::highlight::{highlight, Colour, Modifier};
use hash_error_codes::error_codes::HashErrorCode;
use hash_source::location::SourceLocation;

/// A data type representing a comment/message on a specific span in a code
/// block.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct ReportCodeBlockInfo {
    /// How many characters should be used for line numbers on the side.
    pub indent_width: usize,
    /// The beginning column of the code block.
    pub start_col: usize,
    /// The beginning row of the code block.
    pub start_row: usize,
    /// The end column of the code block.
    pub end_col: usize,
    /// The end row of the code block.
    pub end_row: usize,
}

/// Enumeration describing the kind of [Report]; either being a warning, info or
/// an error.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ReportKind {
    /// The report is an error.
    Error,
    /// The report is an informational diagnostic (likely for internal
    /// purposes).
    Info,
    /// The report is a warning.
    Warning,
    // This is an internal compiler error.
    Internal,
}

impl ReportKind {
    /// Get the [Colour] of the label associated with the [ReportKind].
    pub(crate) fn as_colour(&self) -> Colour {
        match self {
            ReportKind::Error | ReportKind::Internal => Colour::Red,
            ReportKind::Info => Colour::Blue,
            ReportKind::Warning => Colour::Yellow,
        }
    }

    /// Get the string label associated with the [ReportKind].
    pub(crate) fn message(&self) -> &'static str {
        match self {
            ReportKind::Error => "error",
            ReportKind::Internal => "internal",
            ReportKind::Info => "info",
            ReportKind::Warning => "warn",
        }
    }
}

impl fmt::Display for ReportKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", highlight(self.as_colour() | Modifier::Bold, self.message()))
    }
}

/// The kind of [ReportNote], this is primarily used for rendering the label of
/// the [ReportNote].
#[derive(Debug, Clone)]
pub enum ReportNoteKind {
    /// A help message or a suggestion.
    Help,
    /// Information note
    Info,
    /// Additional information about the diagnostic.
    Note,
}

impl fmt::Display for ReportNoteKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReportNoteKind::Note => write!(f, "note"),
            ReportNoteKind::Info => write!(f, "info"),
            ReportNoteKind::Help => write!(f, "{}", highlight(Colour::Cyan, "help")),
        }
    }
}

/// Data type representing a report note which consists of a label and the
/// message.
#[derive(Debug, Clone)]
pub struct ReportNote {
    pub label: ReportNoteKind,
    pub message: String,
}

impl ReportNote {
    pub fn new(label: ReportNoteKind, message: impl ToString) -> Self {
        Self { label, message: message.to_string() }
    }
}

/// Data structure representing an associated block of code with a report. The
/// type contains the span of the block, the message associated with a block and
/// optional [ReportCodeBlockInfo] which adds a message pointed to a code item.
#[derive(Debug, Clone)]
pub struct ReportCodeBlock {
    pub source_location: SourceLocation,
    pub code_message: String,
    pub(crate) info: Cell<Option<ReportCodeBlockInfo>>,
}

impl ReportCodeBlock {
    /// Create a new [ReportCodeBlock] from a [SourceLocation] and a message.
    pub fn new(source_location: SourceLocation, code_message: impl ToString) -> Self {
        Self { source_location, code_message: code_message.to_string(), info: Cell::new(None) }
    }
}

/// Enumeration representing types of components of a [Report]. A [Report] can
/// be made of either [ReportCodeBlock]s or [ReportNote]s.
#[derive(Debug, Clone)]
pub enum ReportElement {
    CodeBlock(ReportCodeBlock),
    Note(ReportNote),
}

/// The report data type represents the entire report which might contain many
/// [ReportElement]s. The report also contains a general [ReportKind] and a
/// general message.
#[derive(Debug, Clone)]
pub struct Report {
    /// The general kind of the report.
    pub kind: ReportKind,
    /// A general associated message with the report.
    pub message: String,
    /// An optional associated general error code with the report.
    pub error_code: Option<HashErrorCode>,
    /// A vector of additional [ReportElement]s in order to add additional
    /// context to errors.
    pub contents: Vec<ReportElement>,
}

impl Report {
    /// Check if the report denotes an occurred error.
    pub fn is_error(&self) -> bool {
        self.kind == ReportKind::Error
    }

    /// Check if the report denotes an occurred warning.
    pub fn is_warning(&self) -> bool {
        self.kind == ReportKind::Warning
    }
}
