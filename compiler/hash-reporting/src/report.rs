//! Hash diagnostic report data structures.
use std::{cell::OnceCell, fmt};

use hash_error_codes::error_codes::HashErrorCode;
use hash_source::{
    location::{RowColRange, Span},
    SourceMapUtils,
};
use hash_utils::highlight::{highlight, Colour, Modifier};

/// A data type representing a comment/message on a specific span in a code
/// block.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct ReportCodeBlockInfo {
    /// How many characters should be used for line numbers on the side.
    pub indent_width: usize,

    /// The span of the code block but using row and column indices.
    pub span: RowColRange,
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReportNoteKind {
    /// A help message or a suggestion.
    Help,

    /// Information note
    Info,

    /// Additional information about the diagnostic.
    Note,

    /// An empty marker that is used to just add a `=` line.
    Raw,
}

impl ReportNoteKind {
    /// Get the string representation of the label.
    pub fn as_str(&self) -> &'static str {
        match self {
            ReportNoteKind::Note => "note",
            ReportNoteKind::Info => "info",
            ReportNoteKind::Help => "help",
            ReportNoteKind::Raw => "",
        }
    }
}

impl fmt::Display for ReportNoteKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReportNoteKind::Note => write!(f, "note"),
            ReportNoteKind::Info => write!(f, "info"),
            ReportNoteKind::Raw => Ok(()),
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
    pub span: Span,
    pub code_message: String,
    pub(crate) info: OnceCell<ReportCodeBlockInfo>,
}

impl ReportCodeBlock {
    /// Create a new [ReportCodeBlock] from a [Span] and a message.
    pub fn new(source_location: Span, code_message: impl ToString) -> Self {
        Self {
            span: source_location,
            code_message: code_message.to_string(),
            info: OnceCell::new(),
        }
    }
}

/// Enumeration representing types of components of a [Report]. A [Report] can
/// be made of either [ReportCodeBlock]s or [ReportNote]s.
#[derive(Debug, Clone)]
pub enum ReportElement {
    CodeBlock(ReportCodeBlock),
    Note(ReportNote),
}

/// Create a `help` note with the given message.
pub macro help {
    ($($arg:tt)*) => {
        ReportElement::Note(ReportNote::new(ReportNoteKind::Help, format!($($arg)*)))
    }
}

/// Create a `note` note with the given message.
pub macro note {
    ($($arg:tt)*) => {
        ReportElement::Note(ReportNote::new(ReportNoteKind::Note, format!($($arg)*)))
    }
}

/// Create a `info` note with the given message.
pub macro info {
    ($($arg:tt)*) => {
        ReportElement::Note(ReportNote::new(ReportNoteKind::Info, format!($($arg)*)))
    }
}

/// The report data type represents the entire report which might contain many
/// [ReportElement]s. The report also contains a general [ReportKind] and a
/// general message.
#[derive(Debug, Clone)]
pub struct Report {
    /// The general kind of the report.
    pub kind: ReportKind,
    /// A title for the report.
    pub title: String,
    /// An optional associated general error code with the report.
    pub error_code: Option<HashErrorCode>,
    /// A vector of additional [ReportElement]s in order to add additional
    /// context to errors.
    pub contents: Vec<ReportElement>,
}

impl Report {
    pub fn new() -> Self {
        Self::default()
    }

    /// Check if the report denotes an occurred error.
    pub fn is_error(&self) -> bool {
        self.kind == ReportKind::Error
    }

    /// Check if the report denotes an occurred warning.
    pub fn is_warning(&self) -> bool {
        self.kind == ReportKind::Warning
    }

    /// Add a title to the [Report].
    pub fn title(&mut self, title: impl ToString) -> &mut Self {
        self.title = title.to_string();
        self
    }

    /// Add a general kind to the [Report].
    pub fn kind(&mut self, kind: ReportKind) -> &mut Self {
        self.kind = kind;
        self
    }

    /// Add an associated [HashErrorCode] to the [Report].
    pub fn code(&mut self, error_code: HashErrorCode) -> &mut Self {
        self.error_code = Some(error_code);
        self
    }

    /// Add a [`ReportNoteKind::Help`] note with the given message to the
    /// [Report].
    pub fn add_help(&mut self, message: impl ToString) -> &mut Self {
        self.add_element(ReportElement::Note(ReportNote::new(
            ReportNoteKind::Help,
            message.to_string(),
        )))
    }

    /// Add a [`ReportNoteKind::Info`] note with the given message to the
    /// [Report].
    pub fn add_info(&mut self, message: impl ToString) -> &mut Self {
        self.add_element(ReportElement::Note(ReportNote::new(
            ReportNoteKind::Info,
            message.to_string(),
        )))
    }

    /// Add a [`ReportNoteKind::Empty`] note with the given message to the
    /// [Report].
    pub fn add_empty(&mut self, message: impl ToString) -> &mut Self {
        self.add_element(ReportElement::Note(ReportNote::new(
            ReportNoteKind::Raw,
            message.to_string(),
        )))
    }

    /// Add a [`ReportNoteKind::Note`] note with the given message to the
    /// [Report].
    pub fn add_note(&mut self, message: impl ToString) -> &mut Self {
        self.add_element(ReportElement::Note(ReportNote::new(
            ReportNoteKind::Note,
            message.to_string(),
        )))
    }

    /// Add a code block at the given location to the [Report].
    pub fn add_span(&mut self, location: Span) -> &mut Self {
        self.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(location, "")))
    }

    /// Add a labelled code block at the given location to the [Report].
    pub fn add_labelled_span(&mut self, location: Span, message: impl ToString) -> &mut Self {
        self.add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
            location,
            message.to_string(),
        )))
    }

    /// Add a [ReportElement] to the report.
    pub fn add_element(&mut self, element: ReportElement) -> &mut Self {
        self.contents.push(element);
        self
    }
}

impl Default for Report {
    fn default() -> Self {
        Self {
            kind: ReportKind::Error,
            title: "Bottom text".to_string(),
            error_code: None,
            contents: vec![],
        }
    }
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Add the optional error code to the general message...
        let error_code_fmt = match self.error_code {
            Some(error_code) => highlight(
                self.kind.as_colour() | Modifier::Bold,
                format!("[{:0>4}]", error_code.to_num()),
            ),
            None => String::new(),
        };

        // Add the general note about the report...
        writeln!(f, "{}{}: {}", self.kind, error_code_fmt, highlight(Modifier::Bold, &self.title),)?;

        let longest_indent_width =
            self.contents.iter().fold(0, |longest_indent_width, element| match element {
                ReportElement::CodeBlock(code_block) => {
                    SourceMapUtils::map(code_block.span.id, |source| {
                        code_block.info(source).indent_width.max(longest_indent_width)
                    })
                }
                ReportElement::Note(_) => longest_indent_width,
            });

        let mut iter = self.contents.iter().peekable();

        while let Some(note) = iter.next() {
            note.render(f, longest_indent_width, self.kind)?;

            if matches!(iter.peek(), Some(ReportElement::CodeBlock(_))) {
                writeln!(f)?;
            }
        }

        Ok(())
    }
}
