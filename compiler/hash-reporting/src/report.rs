use std::{
    cell::Cell,
    fmt,
    iter::{once, repeat},
};

use hash_error_codes::error_codes::HashErrorCode;
use hash_source::{location::SourceLocation, SourceMap};
use hash_utils::path::adjust_canonicalization;

use crate::{
    highlight::{highlight, Colour, Modifier},
    writer::{offset_col_row, ReportCodeBlockInfo, ERROR_MARKING_CHAR},
};

/// Enumeration describing the kind of [Report]; either being a warning, info or a
/// error.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ReportKind {
    /// The report is an error.
    Error,
    /// The report is an informational diagnostic(likely for internal purposes).
    Info,
    /// The report is a warning.
    Warning,
    // @@TODO: Add `Internal` variant: This is an internal compiler error.
}

impl ReportKind {
    /// Get the [Colour] of the label associated with the [ReportKind].
    pub(crate) fn as_colour(&self) -> Colour {
        match self {
            ReportKind::Error => Colour::Red,
            ReportKind::Info => Colour::Blue,
            ReportKind::Warning => Colour::Yellow,
        }
    }

    /// Get the string label associated with the [ReportKind].
    pub(crate) fn message(&self) -> &'static str {
        match self {
            ReportKind::Error => "error",
            ReportKind::Info => "info",
            ReportKind::Warning => "warn",
        }
    }
}

impl fmt::Display for ReportKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            highlight(self.as_colour() | Modifier::Bold, self.message())
        )
    }
}

/// The kind of [ReportNote], this is primarily used for rendering the label of the
/// [ReportNote].
#[derive(Debug, Clone)]
pub enum ReportNoteKind {
    /// A help message or a suggestion.
    Help,
    /// Additional information about the diagnostic.
    Note,
}

impl fmt::Display for ReportNoteKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReportNoteKind::Note => write!(f, "note"),
            ReportNoteKind::Help => write!(f, "{}", highlight(Colour::Cyan, "help")),
        }
    }
}

/// Data type representing a report note which consists of a label and the message.
#[derive(Debug, Clone)]
pub struct ReportNote {
    pub label: ReportNoteKind,
    pub message: String,
}

impl ReportNote {
    pub fn new(label: ReportNoteKind, message: impl ToString) -> Self {
        Self {
            label,
            message: message.to_string(),
        }
    }

    fn render(&self, f: &mut fmt::Formatter<'_>, longest_indent_width: usize) -> fmt::Result {
        writeln!(
            f,
            "{} {} {}: {}",
            " ".repeat(longest_indent_width),
            highlight(Colour::Blue, "="),
            highlight(Modifier::Bold, &self.label),
            self.message
        )?;

        Ok(())
    }
}

/// Data structure representing an associated block of code with a report. The type
/// contains the span of the block, the message associated with a block and optional
/// [ReportCodeBlockInfo] which adds a message pointed to a code item.
#[derive(Debug, Clone)]
pub struct ReportCodeBlock {
    pub source_location: SourceLocation,
    pub code_message: String,
    pub(crate) info: Cell<Option<ReportCodeBlockInfo>>,
}

impl ReportCodeBlock {
    /// Create a new [ReportCodeBlock] from a [SourceLocation] and a message.
    pub fn new(source_location: SourceLocation, code_message: impl ToString) -> Self {
        Self {
            source_location,
            code_message: code_message.to_string(),
            info: Cell::new(None),
        }
    }

    // Get the indent widths of this code block as (outer, inner).
    pub(crate) fn info<T: SourceMap>(&self, modules: &T) -> ReportCodeBlockInfo {
        match self.info.get() {
            Some(info) => info,
            None => {
                let source_id = self.source_location.source_id;
                let source = modules.contents_by_id(source_id);

                let location = self.source_location.span;

                let (start_col, start_row) = offset_col_row(location.start(), source);
                let (end_col, end_row) = offset_col_row(location.end(), source);
                let (_, last_row) = offset_col_row(source.len(), source);

                let (top_buf, bottom_buf) = compute_buffers(start_row, end_row);
                let indent_width = (start_row.saturating_sub(top_buf) + 1)
                    .max((end_row + bottom_buf).min(last_row) + 1)
                    .to_string()
                    .chars()
                    .count();

                let info = ReportCodeBlockInfo {
                    indent_width,
                    start_col,
                    start_row,
                    end_col,
                    end_row,
                };

                self.info.replace(Some(info));
                info
            }
        }
    }

    /// Function to render the [ReportCodeBlock] using the provided [SourceLocation], message and
    /// [ReportKind].
    fn render<T: SourceMap>(
        &self,
        f: &mut fmt::Formatter,
        modules: &T,
        longest_indent_width: usize,
        report_kind: ReportKind,
    ) -> fmt::Result {
        // Print line numbers, separator, then the code itself, split by newlines
        // Should put the code_message where it is supposed to be with a caret (^) followed by (_)
        // or equivalent unicode character.
        //
        // Print a few lines before and after location/code_message.
        let source_id = self.source_location.source_id;
        let source = modules.contents_by_id(source_id);
        let ReportCodeBlockInfo {
            start_row,
            end_row,
            start_col,
            end_col,
            ..
        } = self.info(modules);

        let (top_buffer, bottom_buffer) = compute_buffers(start_row, end_row);

        let error_view = source
            .trim_end_matches('\n')
            .split('\n')
            .enumerate()
            .skip(start_row.saturating_sub(top_buffer))
            .take(top_buffer + end_row - start_row + 1 + bottom_buffer);

        // Print the filename of the code block...
        writeln!(
            f,
            "{}{} {}",
            " ".repeat(longest_indent_width),
            highlight(Colour::Blue, "-->"),
            highlight(
                Modifier::Underline,
                format!(
                    "{}:{}:{}",
                    adjust_canonicalization(modules.path_by_id(source_id)),
                    start_row + 1,
                    start_col + 1,
                )
            )
        )?;

        // Print each selected line with the line number
        for (index, line) in error_view {
            let index_str = format!(
                "{:>pad_width$}",
                index + 1,
                pad_width = longest_indent_width
            );

            writeln!(
                f,
                "{} {}   {}",
                if (start_row..=end_row).contains(&index) && !line.is_empty() {
                    highlight(report_kind.as_colour(), &index_str)
                } else {
                    index_str
                },
                highlight(Colour::Blue, "|"),
                line
            )?;

            if (start_row..=end_row).contains(&index) && !line.is_empty() {
                let dashes = repeat(ERROR_MARKING_CHAR).take(
                    if index == start_row && start_row == end_row {
                        end_col - start_col
                    } else if index == start_row {
                        line.len().saturating_sub(start_col)
                    } else if index == end_row {
                        end_col
                    } else {
                        line.len()
                    },
                );

                let mut code_note: String = repeat(" ")
                    .take(if index == start_row { start_col } else { 0 })
                    .chain(dashes)
                    .collect();

                if index == end_row {
                    code_note.extend(once(" ").chain(once(self.code_message.as_str())));
                }

                writeln!(
                    f,
                    "{} {}   {}",
                    " ".repeat(longest_indent_width),
                    highlight(Colour::Blue, "|"),
                    highlight(report_kind.as_colour(), &code_note)
                )?;
            }
        }

        Ok(())
    }
}

/// Compute the top buffer and bottom buffer sizes from the given start and
/// end row for a code block.
fn compute_buffers(start_row: usize, end_row: usize) -> (usize, usize) {
    const MAX_BUFFER: usize = 5;
    let top_buffer: usize = (end_row - start_row + 1).min(MAX_BUFFER);
    let bottom_buffer: usize = (end_row - start_row + 1).min(MAX_BUFFER);
    (top_buffer, bottom_buffer)
}

/// Enumeration representing types of components of a [Report]. A [Report] can be made of
/// either [ReportCodeBlock]s or [ReportNote]s.
#[derive(Debug, Clone)]
pub enum ReportElement {
    CodeBlock(ReportCodeBlock),
    Note(ReportNote),
}

impl ReportElement {
    pub(crate) fn render<T: SourceMap>(
        &self,
        f: &mut fmt::Formatter,
        modules: &T,
        longest_indent_width: usize,
        report_kind: ReportKind,
    ) -> fmt::Result {
        match self {
            ReportElement::CodeBlock(code_block) => {
                code_block.render(f, modules, longest_indent_width, report_kind)
            }
            ReportElement::Note(note) => note.render(f, longest_indent_width),
        }
    }
}

/// The report data type represents the entire report which might contain many [ReportElement]s. The
/// report also contains a general [ReportKind] and a general message.
#[derive(Debug, Clone)]
pub struct Report {
    /// The general kind of the report.
    pub kind: ReportKind,
    /// A general associated message with the report.
    pub message: String,
    /// An optional associated general error code with the report.
    pub error_code: Option<HashErrorCode>,
    /// A vector of additional [ReportElement]s in order to add additional context
    /// to errors.
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
