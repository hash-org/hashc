//! Hash Compiler error and warning reporting module.
use crate::highlight::{highlight, Colour, Modifier};
use core::fmt;
use hash_error_codes::error_codes::HashErrorCode;
use hash_source::{location::SourceLocation, SourceMap};
use hash_utils::path::adjust_canonicalization;
use std::{
    cell::Cell,
    iter::{once, repeat},
};

const ERROR_MARKING_CHAR: &str = "^";

/// Enumeration describing the type of report; either being a warning, info or a
/// error.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ReportKind {
    Error,
    Info,
    Warning,
}

impl ReportKind {
    /// Get the [Colour] of the label associated with the [ReportKind].
    fn as_colour(&self) -> Colour {
        match self {
            ReportKind::Error => Colour::Red,
            ReportKind::Info => Colour::Blue,
            ReportKind::Warning => Colour::Yellow,
        }
    }

    /// Get the string label associated with the [ReportKind].
    fn message(&self) -> &'static str {
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
#[derive(Debug, Clone)]
pub enum ReportNoteKind {
    Help,
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
    info: Cell<Option<ReportCodeBlockInfo>>,
}

/// A data type representing a comment/message on a specific span in a code block.
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

/// Function to compute a row and column number from a given source string
/// and an offset within the source. This will take into account the number
/// of encountered newlines and characters per line in order to compute
/// precise row and column numbers of the span.
fn offset_col_row(offset: usize, source: &str) -> (usize, usize) {
    let source_lines = source.split('\n');

    let mut bytes_skipped = 0;
    let mut total_lines: usize = 0;
    let mut last_line_len = 0;

    let mut line_index = None;
    for (line_idx, line) in source_lines.enumerate() {
        // One byte for the newline
        let skip_width = line.len() + 1;

        if (bytes_skipped..=bytes_skipped + skip_width).contains(&offset) {
            line_index = Some((offset - bytes_skipped, line_idx));
            break;
        }

        bytes_skipped += skip_width;
        total_lines += 1;
        last_line_len = line.len();
    }

    line_index.unwrap_or((
        last_line_len.saturating_sub(1),
        total_lines.saturating_sub(1),
    ))
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
    fn info<T: SourceMap>(&self, modules: &T) -> ReportCodeBlockInfo {
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
                if (start_row..=end_row).contains(&index) {
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
    fn render<T: SourceMap>(
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

#[derive(Debug, Default)]
pub struct ReportBuilder {
    kind: Option<ReportKind>,
    message: Option<String>,
    error_code: Option<HashErrorCode>,
    contents: Vec<ReportElement>,
}

/// A [Report] builder trait.
impl ReportBuilder {
    /// Initialise a new [ReportBuilder].
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a general message to the [Report].
    pub fn with_message(&mut self, message: impl ToString) -> &mut Self {
        self.message = Some(message.to_string());
        self
    }

    /// Add a general kind to the [Report].
    pub fn with_kind(&mut self, kind: ReportKind) -> &mut Self {
        self.kind = Some(kind);
        self
    }

    /// Add an associated [HashErrorCode] to the [Report].
    pub fn with_error_code(&mut self, error_code: HashErrorCode) -> &mut Self {
        self.error_code = Some(error_code);
        self
    }

    /// Add a [ReportElement] to the report.
    pub fn add_element(&mut self, element: ReportElement) -> &mut Self {
        self.contents.push(element);
        self
    }

    /// Create a [Report] from the [ReportBuilder].
    pub fn build(&mut self) -> Report {
        Report {
            kind: self.kind.take().unwrap(),
            message: self.message.take().unwrap(),
            error_code: self.error_code.take(),
            contents: std::mem::take(&mut self.contents),
        }
    }
}

/// General data type for displaying [Report]s. This is needed due to the
/// [Report] rendering process needing access to the program modules to get
/// access to the source code.
pub struct ReportWriter<'m, T: SourceMap> {
    report: Report,
    sources: &'m T,
}

impl<'m, T: SourceMap> ReportWriter<'m, T> {
    pub fn new(report: Report, sources: &'m T) -> Self {
        Self { report, sources }
    }
}

impl<T: SourceMap> fmt::Display for ReportWriter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Add the optional error code to the general message...
        let error_code_fmt = match self.report.error_code {
            Some(error_code) => highlight(
                self.report.kind.as_colour() | Modifier::Bold,
                format!("[{:0>4}]", error_code.to_num()),
            ),
            None => String::new(),
        };

        // Add the general note about the report...
        writeln!(
            f,
            "{}{}: {}",
            self.report.kind,
            error_code_fmt,
            highlight(Modifier::Bold, &self.report.message),
        )?;

        let longest_indent_width =
            self.report
                .contents
                .iter()
                .fold(0, |longest_indent_width, element| match element {
                    ReportElement::CodeBlock(code_block) => code_block
                        .info(self.sources)
                        .indent_width
                        .max(longest_indent_width),
                    ReportElement::Note(_) => longest_indent_width,
                });

        let mut iter = self.report.contents.iter().peekable();

        while let Some(note) = iter.next() {
            note.render(f, self.sources, longest_indent_width, self.report.kind)?;

            if matches!(iter.peek(), Some(ReportElement::CodeBlock(_))) {
                writeln!(f)?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    // use std::path::PathBuf;

    // use hash_alloc::{row, Castle};
    // use hash_ast::{ast, location::Location, module::ModuleBuilder};

    use super::*;

    // #[test]
    // fn reporting_test() {
    //     let castle = Castle::new();
    //     let wall = castle.wall();

    //     let builder = ModuleBuilder::new();

    //     let path = PathBuf::from("./../../stdlib/prelude.hash");
    //     let contents = std::fs::read_to_string(&path).unwrap();
    //     let test_idx = builder.reserve_index();

    //     builder.add_contents(test_idx, path, contents);
    //     builder.add_module_at(
    //         test_idx,
    //         ast::AstNode::new(
    //             ast::Module {
    //                 contents: row![&wall],
    //             },
    //             Location::pos(0),
    //             &wall,
    //         ),
    //     );

    //     let modules = builder.build();

    //     let report = ReportBuilder::new()
    //         .with_message("Bro what you wrote here is wrong.")
    //         .with_kind(ReportKind::Error)
    //         .with_error_code(ErrorCode::Parsing)
    //         .add_element(ReportElement::CodeBlock(ReportCodeBlock::new(
    //             SourceLocation {
    //                 location: Location::span(10223, 10224),
    //                 module_index: test_idx,
    //             },
    //             "don't be crazy.",
    //         )))
    //         .add_element(ReportElement::Note(ReportNote::new(
    //             "note",
    //             "You really are a dummy.",
    //         )))
    //         .build()
    //         .unwrap();

    //     let report_writer = ReportWriter::new(report, &modules);

    //     println!("{}", report_writer);
    // }

    #[test]
    fn offset_test() {
        let contents = "Hello, world!\nGoodbye, world, it has been fun.";

        let (col, row) = offset_col_row(contents.len() - 1, contents);
        assert_eq!((col, row), (31, 1));

        let (col, row) = offset_col_row(contents.len() + 3, contents);
        assert_eq!((col, row), (31, 1));
    }
}
