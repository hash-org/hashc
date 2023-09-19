//! Hash diagnostic report rendering logic. Within this renderer,
//! there are currently two modes: `line` and `block`. Within this
//! module, the modes are often referred to either being line or block.
//! The difference between the two modes is how they are displayed
//! when rendered. The `line` mode is designed to highlight spans that
//! are contained to a single line, whereas `block` mode is designed to
//! for bulkier spans that might take up many lines. More specific examples
//! of both modes are located in the documentation of the functions
//! that are responsible for rendering either mode.

use std::{
    fmt,
    iter::{once, repeat},
};

use hash_source::{
    location::{RowColRange, Span},
    Source, SourceMapUtils,
};
use hash_utils::{
    highlight::{highlight, Colour, Modifier},
    range_map::Range,
};

use crate::report::{
    ReportCodeBlock, ReportCodeBlockInfo, ReportElement, ReportKind, ReportNote, ReportNoteKind,
};

/// Character used to denote the span of the diagnostic for the `line` view.
const LINE_DIAGNOSTIC_MARKER: char = '^';

/// Character used to denote the span of the diagnostic for the `block` view.
const BLOCK_DIAGNOSTIC_MARKER: char = '-';

/// Character used to connect block views
const DIAGNOSTIC_CONNECTING_CHAR: &str = "|";

/// The maximum number of lines a block display can use before the lines in the
/// center of the block are skipped.
const LINE_SKIP_THRESHOLD: usize = 6;

/// This function holds inner rules for calculating what the selected top
/// and bottom buffer sizes should be.
fn adjust_initial_span_size(span: usize) -> usize {
    // @@Correctness: This is an arbitrary rule and should be decided upon more
    // concretely. It's even possible that we might not want to get any additional
    // lines for even larger spans
    match span {
        3..=4 => 2,
        5.. => 1,
        _ => span,
    }
}

/// Compute the top buffer and bottom buffer sizes from the given start and
/// end row for a code block.
fn compute_buffers(start_row: usize, end_row: usize) -> (usize, usize) {
    const MAX_BUFFER: usize = 5;

    let diff = adjust_initial_span_size(end_row - start_row + 1);

    // Cap the buffers to a maximum of 5
    let top_buffer = diff.min(MAX_BUFFER);
    let bottom_buffer = diff.min(MAX_BUFFER);

    (top_buffer, bottom_buffer)
}

impl ReportCodeBlock {
    // Get the indent widths of this code block as (outer, inner).
    pub(crate) fn info(&self, source: &Source) -> &ReportCodeBlockInfo {
        self.info.get_or_init(|| {
            let Span { range, .. } = self.span;
            let ranges = source.line_ranges();
            let (start, end, last) = (
                ranges.get_row_col(range.start(), false),
                // The `end` of a span is considered to be inclusive!
                ranges.get_row_col(range.end(), true),
                ranges.get_row_col(source.contents().0.len() - 1, false),
            );

            // Compute the selected span outside of the diagnostic span
            let (top_buf, bottom_buf) = compute_buffers(start.row, end.row);

            // Compute the size of the indent based on the line numbers
            let indent_width = (start.row.saturating_sub(top_buf) + 1)
                .max((end.row + bottom_buf).min(last.row) + 1)
                .to_string()
                .chars()
                .count();

            let span = RowColRange::new(start, end);
            ReportCodeBlockInfo { indent_width, span }
        })
    }

    /// Function to extract the block of the code that will be used to display
    /// the span of the diagnostic.
    fn get_source_view<'a>(&self, source: &'a Source) -> impl Iterator<Item = (usize, &'a str)> {
        let ReportCodeBlockInfo { span, .. } = self.info(source);
        let (start_row, end_row) = span.rows();
        let (top_buffer, bottom_buffer) = compute_buffers(start_row, end_row);

        // Get the actual contents of the erroneous span
        source
            .contents()
            .0
            .lines()
            .enumerate()
            .skip(start_row.saturating_sub(top_buffer))
            .take(top_buffer + end_row - start_row + 1 + bottom_buffer)
    }

    /// Function that performs the rendering of the `line` view for a
    /// diagnostic. In this mode, only a single line is highlighted using
    /// the [LINE_DIAGNOSTIC_MARKER]. It will highlight the entire span
    /// using this mode. Here is an example of a diagnostic using the `line`
    /// mode:
    ///
    /// ```text
    /// error: non-declarative expressions are not allowed in `module` pattern
    /// --> ~/examples/weird.hash:1:1
    /// 1 |   a = "2";
    ///   |   ^^^^^^^ not allowed here
    /// 2 |
    /// 3 |   // main := () => {
    /// ```
    fn render_line_view(
        &self,
        f: &mut fmt::Formatter,
        source: &Source,
        longest_indent_width: usize,
        kind: ReportKind,
    ) -> fmt::Result {
        let error_view = self.get_source_view(source);
        let ReportCodeBlockInfo { span, .. } = self.info(source);

        let (start_row, end_row) = span.rows();
        let (start_column, end_column) = span.columns();

        // Print each selected line with the line number
        for (index, line) in error_view {
            let index_str = format!("{:>longest_indent_width$}", index + 1);

            let line_number = if (start_row..=end_row).contains(&index) {
                highlight(kind.as_colour(), &index_str)
            } else {
                index_str
            };

            writeln!(f, "{line_number} {}   {line}", highlight(Colour::Blue, "|"))?;

            if (start_row..=end_row).contains(&index) && !line.is_empty() {
                let dashes: String = repeat(LINE_DIAGNOSTIC_MARKER)
                    .take(if index == start_row && start_row == end_row {
                        end_column - start_column
                    } else if index == start_row {
                        line.len().saturating_sub(start_column)
                    } else if index == end_row {
                        end_column
                    } else {
                        line.len()
                    })
                    .collect();

                let mut code_note: String = repeat(" ")
                    .take(if index == start_row { start_column } else { 0 })
                    .chain(once(dashes.as_str()))
                    .collect();

                if index == end_row {
                    code_note.extend(once(" ").chain(once(self.code_message.as_str())));
                }

                writeln!(
                    f,
                    "{} {}   {}",
                    " ".repeat(longest_indent_width),
                    highlight(Colour::Blue, "|"),
                    highlight(kind.as_colour(), &code_note)
                )?;
            }
        }

        Ok(())
    }

    /// Function that performs the rendering of the `block` view for a
    /// diagnostic. The `block` view works by drawing an initial arrow that
    /// points to the start of the diagnostic span, and an arrow to the end
    /// of the span in the same format (with a label at the end). The two
    /// arrows are connected by a vertical connector on the left hand-side.
    /// Here is an example of the `block` mode:
    ///
    /// ```text
    /// error: non-declarative expressions are not allowed in `module` pattern
    ///   --> /Users/alex/Documents/hash-org/hashc/examples/weird.hash:11:1
    ///  9 |    // };
    /// 10 |
    /// 11 |    IoError = struct(
    ///    |  __-
    /// 12 | |      error: IoErrorType,
    /// 13 | |      message: str,
    /// 14 | |  );
    ///    | |___- not allowed here
    /// 15 |
    /// 16 |    // Make this a test case:
    /// ```
    ///
    /// As seen in this example, there are two arrows which look like `__-` and
    /// which are connected by a vertical arrow on the left side of the
    /// span.
    fn render_block_view(
        &self,
        f: &mut fmt::Formatter,
        source: &Source,
        longest_indent_width: usize,
        report_kind: ReportKind,
    ) -> fmt::Result {
        let error_view = self.get_source_view(source);
        let ReportCodeBlockInfo { span, .. } = self.info(source);

        // If the difference between the rows is longer than `LINE_SKIP_THRESHOLD`
        // lines, then we essentially begin to collapse the view by using `...`
        // as the filler for those lines...
        let (start_row, end_row) = span.rows();
        let (start_column, end_column) = span.columns();

        let skip_lines_range = if end_row - start_row > LINE_SKIP_THRESHOLD {
            let mid = LINE_SKIP_THRESHOLD / 2;
            Some(Range::new(start_row + mid, end_row - mid))
        } else {
            None
        };

        // So here, we want to iterate over all of the line and on the starting line, we
        // want to draw an arrow from the left hand-side up until the beginning
        // which then points up, on lines that are in the middle, we just want
        // to draw a connecting character of the arrow, and finally on the line
        // below the final line we want to draw an arrow leading up until
        // the end of the span.
        for (index, line) in error_view {
            let index_str = format!("{:<longest_indent_width$}", index + 1);

            let line_number = if (start_row..=end_row).contains(&index) {
                highlight(report_kind.as_colour(), &index_str)
            } else {
                index_str
            };

            // Compute the connector, if the current index is within the diagnostic span, we
            // also need to add a connector that connects the bottom and top
            // spans by a vertical line to the left hand-side of the diagnostic
            // span.
            let connector = if (start_row + 1..=end_row).contains(&index) {
                DIAGNOSTIC_CONNECTING_CHAR
            } else {
                " "
            };

            // So if we're at the start of the 'skip' range, use '...' instead
            if let Some(range) = skip_lines_range {
                if range.start() == index {
                    let range_line_number = format!(
                        "{:<pad_width$}",
                        ".".repeat(3),
                        pad_width = longest_indent_width + 2
                    );

                    // Write the skipped lines as `...` and then the rest of the components that are
                    // required for the error display
                    writeln!(
                        f,
                        "{} {}",
                        highlight(report_kind.as_colour(), range_line_number),
                        highlight(report_kind.as_colour(), connector),
                    )?;
                }

                // Skip the lines
                if range.contains(index) {
                    continue;
                }
            }

            writeln!(
                f,
                "{} {} {}  {}",
                line_number,
                highlight(Colour::Blue, "|"),
                highlight(report_kind.as_colour(), connector),
                line
            )?;

            // If this is th first row of the diagnostic span, then we want to draw an arrow
            // leading up to it
            if index == start_row {
                let arrow: String = repeat('_')
                    .take(start_column + 2)
                    .chain(once(BLOCK_DIAGNOSTIC_MARKER))
                    .collect();

                writeln!(
                    f,
                    "{} {}  {}",
                    " ".repeat(longest_indent_width),
                    highlight(Colour::Blue, "|"),
                    highlight(report_kind.as_colour(), arrow)
                )?;
            }

            // Now we perform the same operator for creating an arrow to join the end span,
            // and of course we write the note at the end of the span.
            if index == end_row {
                let arrow: String = once('|')
                    .chain(repeat('_').take(end_column + 1))
                    .chain(format!("{BLOCK_DIAGNOSTIC_MARKER} ").chars())
                    .chain(self.code_message.as_str().chars())
                    .collect();

                writeln!(
                    f,
                    "{} {} {}",
                    " ".repeat(longest_indent_width),
                    highlight(Colour::Blue, "|"),
                    highlight(report_kind.as_colour(), arrow)
                )?;
            }
        }

        Ok(())
    }

    /// Function to render the [ReportCodeBlock] using the provided
    /// [Span], message and [ReportKind].
    pub(crate) fn render(
        &self,
        f: &mut fmt::Formatter,
        longest_indent_width: usize,
        report_kind: ReportKind,
    ) -> fmt::Result {
        SourceMapUtils::map(self.span.id, |source| {
            let ReportCodeBlockInfo { span, .. } = self.info(source);

            // Print the filename of the code block...
            writeln!(
                f,
                "{}{} {}",
                " ".repeat(longest_indent_width),
                highlight(Colour::Blue, "-->"),
                highlight(
                    Modifier::Underline,
                    format!("{}:{}", source.canonicalised_path().display(), span.start)
                )
            )?;

            // Now we can determine whether we want to use the `block` or the `line` view.
            // The block view is for displaying large spans for multiple lines,
            // whilst the line view is for a single line span.
            let (start_row, end_row) = span.rows();

            if start_row == end_row {
                self.render_line_view(f, source, longest_indent_width, report_kind)
            } else {
                self.render_block_view(f, source, longest_indent_width, report_kind)
            }
        })
    }
}

impl ReportNote {
    pub(crate) fn render(
        &self,
        f: &mut fmt::Formatter<'_>,
        longest_indent_width: usize,
    ) -> fmt::Result {
        // If the label is `empty`, then we don't want to render anything
        // except for the message.
        if self.label == ReportNoteKind::Raw {
            return write!(f, "{}", self.message);
        }

        // We want to align the specified message line by line
        // with the `note: ...` label being as the initial suffix
        // of the first line. So, we compute the length of the label,
        // which we will use if we have multiple lines within
        // the message.
        //
        // We add the 4 chars for the `: = `
        let label_length = longest_indent_width + 4 + self.label.as_str().len();

        for (index, line) in self.message.lines().enumerate() {
            // The first line is special because we want to add the
            // note.
            if index == 0 {
                writeln!(
                    f,
                    "{} {} {}: {}",
                    " ".repeat(longest_indent_width),
                    highlight(Colour::Blue, "="),
                    highlight(Modifier::Bold, &self.label),
                    line
                )?;
            } else {
                writeln!(f, "{} {}", " ".repeat(label_length), line)?;
            }
        }

        Ok(())
    }
}

impl ReportElement {
    pub(crate) fn render(
        &self,
        f: &mut fmt::Formatter,
        longest_indent_width: usize,
        report_kind: ReportKind,
    ) -> fmt::Result {
        match self {
            ReportElement::CodeBlock(code_block) => {
                code_block.render(f, longest_indent_width, report_kind)
            }
            ReportElement::Note(note) => note.render(f, longest_indent_width),
        }
    }
}
