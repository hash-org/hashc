//! Hash diagnostic report rendering logic.

use std::{
    fmt,
    iter::{once, repeat},
};

use hash_source::SourceMap;
use hash_utils::path::adjust_canonicalization;

use crate::{
    highlight::{highlight, Colour, Modifier},
    report::{ReportCodeBlock, ReportCodeBlockInfo, ReportElement, ReportKind, ReportNote},
};

/// Character used to denote the location of the error.
pub const ERROR_MARKING_CHAR: &str = "^";

/// Function to compute a row and column number from a given source string
/// and an offset within the source. This will take into account the number
/// of encountered newlines and characters per line in order to compute
/// precise row and column numbers of the span.
pub(crate) fn offset_col_row(
    offset: usize,
    source: &str,
    non_inclusive: bool,
) -> (/* col: */ usize, /* row: */ usize) {
    let source_lines = source.split('\n');

    let mut bytes_skipped = 0;
    let mut total_lines: usize = 0;
    let mut last_line_len = 0;

    let mut line_index = None;
    for (line_idx, line) in source_lines.enumerate() {
        // One byte for the newline
        let skip_width = line.len() + 1;

        // Here, we don't want an inclusive range because we don't want to get the last byte because
        // that will always point to the newline character and this isn't necessary to be included
        // when selecting a span for printing.
        let range = if non_inclusive {
            bytes_skipped..bytes_skipped + skip_width
        } else {
            bytes_skipped..bytes_skipped + skip_width + 1
        };

        if range.contains(&offset) {
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

/// Compute the top buffer and bottom buffer sizes from the given start and
/// end row for a code block.
fn compute_buffers(start_row: usize, end_row: usize) -> (usize, usize) {
    const MAX_BUFFER: usize = 5;
    let top_buffer: usize = (end_row - start_row + 1).min(MAX_BUFFER);
    let bottom_buffer: usize = (end_row - start_row + 1).min(MAX_BUFFER);
    (top_buffer, bottom_buffer)
}

impl ReportCodeBlock {
    // Get the indent widths of this code block as (outer, inner).
    pub(crate) fn info<T: SourceMap>(&self, modules: &T) -> ReportCodeBlockInfo {
        match self.info.get() {
            Some(info) => info,
            None => {
                let source_id = self.source_location.source_id;
                let source = modules.contents_by_id(source_id);

                let location = self.source_location.span;

                let (start_col, start_row) = offset_col_row(location.start(), source, true);
                let (end_col, end_row) = offset_col_row(location.end(), source, false);
                let (_, last_row) = offset_col_row(source.len(), source, false);

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
    pub(crate) fn render<T: SourceMap>(
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offset_test() {
        let contents = "Hello, world!\nGoodbye, world, it has been fun.";

        let (col, row) = offset_col_row(contents.len() - 1, contents, false);
        assert_eq!((col, row), (31, 1));

        let (col, row) = offset_col_row(contents.len() + 3, contents, false);
        assert_eq!((col, row), (31, 1));
    }
}
