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

use hash_source::{location::SourceLocation, SourceMap};
use hash_utils::path::adjust_canonicalisation;

use crate::{
    highlight::{highlight, Colour, Modifier},
    report::{ReportCodeBlock, ReportCodeBlockInfo, ReportElement, ReportKind, ReportNote},
};

/// Character used to denote the span of the diagnostic for the `line` view.
const LINE_DIAGNOSTIC_MARKER: char = '^';

/// Character used to denote the span of the diagnostic for the `block` view.
const BLOCK_DIAGNOSTIC_MARKER: char = '-';

/// Character used to connect block views
const DIAGNOSTIC_CONNECTING_CHAR: &str = "|";

/// Struct to represent the column and row offset produced from converting a
/// [hash_source::location::Span].
pub(crate) struct ColRowOffset {
    /// The column offset.
    col: usize,
    /// The row offset.
    row: usize,
}

/// Function to compute a row and column number from a given source string
/// and an offset within the source. This will take into account the number
/// of encountered newlines and characters per line in order to compute
/// precise row and column numbers of the span.
pub(crate) fn offset_col_row(offset: usize, source: &str, non_inclusive: bool) -> ColRowOffset {
    let source_lines = source.split('\n');

    let mut bytes_skipped = 0;
    let mut total_lines: usize = 0;
    let mut last_line_len = 0;

    let mut line_index = None;
    for (line_idx, line) in source_lines.enumerate() {
        // One byte for the newline
        let skip_width = line.len() + 1;

        // Here, we don't want an inclusive range because we don't want to get the last
        // byte because that will always point to the newline character and this
        // isn't necessary to be included when selecting a span for printing.
        let range = if non_inclusive {
            bytes_skipped..bytes_skipped + skip_width
        } else {
            bytes_skipped..bytes_skipped + skip_width + 1
        };

        if range.contains(&offset) {
            line_index = Some(ColRowOffset { col: offset - bytes_skipped, row: line_idx });
            break;
        }

        bytes_skipped += skip_width;
        total_lines += 1;
        last_line_len = line.len();
    }

    line_index.unwrap_or(ColRowOffset {
        col: last_line_len.saturating_sub(1),
        row: total_lines.saturating_sub(1),
    })
}

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
    pub(crate) fn info(&self, sources: &SourceMap) -> ReportCodeBlockInfo {
        match self.info.get() {
            Some(info) => info,
            None => {
                let SourceLocation { span, id: source_id } = self.source_location;
                let source = sources.contents_by_id(source_id);

                // Compute offset rows and columns from the provided span
                let ColRowOffset { col: start_col, row: start_row } =
                    offset_col_row(span.start(), source, true);

                let ColRowOffset { col: end_col, row: end_row } =
                    offset_col_row(span.end(), source, false);

                let ColRowOffset { row: last_row, .. } =
                    offset_col_row(source.len(), source, false);

                // Compute the selected span outside of the diagnostic span
                let (top_buf, bottom_buf) = compute_buffers(start_row, end_row);

                // Compute the size of the indent based on the line numbers
                let indent_width = (start_row.saturating_sub(top_buf) + 1)
                    .max((end_row + bottom_buf).min(last_row) + 1)
                    .to_string()
                    .chars()
                    .count();

                let info =
                    ReportCodeBlockInfo { indent_width, start_col, start_row, end_col, end_row };

                self.info.replace(Some(info));
                info
            }
        }
    }

    /// Function to extract the block of the code that will be used to display
    /// the span of the diagnostic.
    fn get_source_view<'a>(
        &self,
        modules: &'a SourceMap,
    ) -> impl Iterator<Item = (usize, &'a str)> {
        // Get the actual contents of the erroneous span
        let source_id = self.source_location.id;
        let source = modules.contents_by_id(source_id);

        let ReportCodeBlockInfo { start_row, end_row, .. } = self.info(modules);

        let (top_buffer, bottom_buffer) = compute_buffers(start_row, end_row);

        source
            .trim_end_matches('\n')
            .split('\n')
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
        modules: &SourceMap,
        longest_indent_width: usize,
        report_kind: ReportKind,
    ) -> fmt::Result {
        let error_view = self.get_source_view(modules);

        let ReportCodeBlockInfo { start_row, end_row, start_col, end_col, .. } = self.info(modules);

        // Print each selected line with the line number
        for (index, line) in error_view {
            let index_str = format!("{:>pad_width$}", index + 1, pad_width = longest_indent_width);

            let line_number = if (start_row..=end_row).contains(&index) {
                highlight(report_kind.as_colour(), &index_str)
            } else {
                index_str
            };

            writeln!(f, "{} {}   {}", line_number, highlight(Colour::Blue, "|"), line)?;

            if (start_row..=end_row).contains(&index) && !line.is_empty() {
                let dashes: String = repeat(LINE_DIAGNOSTIC_MARKER)
                    .take(if index == start_row && start_row == end_row {
                        end_col - start_col
                    } else if index == start_row {
                        line.len().saturating_sub(start_col)
                    } else if index == end_row {
                        end_col
                    } else {
                        line.len()
                    })
                    .collect();

                let mut code_note: String = repeat(" ")
                    .take(if index == start_row { start_col } else { 0 })
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
                    highlight(report_kind.as_colour(), &code_note)
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
    ///   --> /Users/alex/Documents/hash-org/lang/examples/weird.hash:11:1
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
        modules: &SourceMap,
        longest_indent_width: usize,
        report_kind: ReportKind,
    ) -> fmt::Result {
        let error_view = self.get_source_view(modules);

        let ReportCodeBlockInfo { start_row, end_row, start_col, end_col, .. } = self.info(modules);

        // So here, we want to iterate over all of the line and on the starting line, we
        // want to draw an arrow from the left hand-side up until the beginning
        // which then points up, on lines that are in the middle, we just want
        // to draw a connecting character of the arrow, and finally on the line
        // below the final line we want to draw an arrow leading up until
        // the end of the span.
        for (index, line) in error_view {
            let index_str = format!("{:>pad_width$}", index + 1, pad_width = longest_indent_width);

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
                let arrow: String =
                    repeat('_').take(start_col + 2).chain(once(BLOCK_DIAGNOSTIC_MARKER)).collect();

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
                    .chain(repeat('_').take(end_col + 2))
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
    /// [SourceLocation], message and [ReportKind].
    pub(crate) fn render(
        &self,
        f: &mut fmt::Formatter,
        modules: &SourceMap,
        longest_indent_width: usize,
        report_kind: ReportKind,
    ) -> fmt::Result {
        let source_id = self.source_location.id;
        let ReportCodeBlockInfo { start_row, end_row, start_col, .. } = self.info(modules);

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
                    adjust_canonicalisation(modules.path_by_id(source_id)),
                    start_row + 1,
                    start_col + 1,
                )
            )
        )?;

        // Now we can determine whether we want to use the `block` or the `line` view.
        // The block view is for displaying large spans for multiple lines,
        // whilst the line view is for a single line span.
        if start_row == end_row {
            self.render_line_view(f, modules, longest_indent_width, report_kind)
        } else {
            self.render_block_view(f, modules, longest_indent_width, report_kind)
        }
    }
}

impl ReportNote {
    pub(crate) fn render(
        &self,
        f: &mut fmt::Formatter<'_>,
        longest_indent_width: usize,
    ) -> fmt::Result {
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

impl ReportElement {
    pub(crate) fn render(
        &self,
        f: &mut fmt::Formatter,
        modules: &SourceMap,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offset_test() {
        let contents = "Hello, world!\nGoodbye, world, it has been fun.";

        let ColRowOffset { col, row } = offset_col_row(contents.len() - 1, contents, false);
        assert_eq!((col, row), (31, 1));

        let ColRowOffset { col, row } = offset_col_row(contents.len() + 3, contents, false);
        assert_eq!((col, row), (31, 1));
    }
}
