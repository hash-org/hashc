use std::fmt;

use hash_source::SourceMap;

use crate::{
    highlight::{highlight, Modifier},
    report::{Report, ReportElement},
};

/// Character used to denote the location of the error.
pub const ERROR_MARKING_CHAR: &str = "^";

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
pub(crate) fn offset_col_row(offset: usize, source: &str) -> (usize, usize) {
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
    use super::*;

    #[test]
    fn offset_test() {
        let contents = "Hello, world!\nGoodbye, world, it has been fun.";

        let (col, row) = offset_col_row(contents.len() - 1, contents);
        assert_eq!((col, row), (31, 1));

        let (col, row) = offset_col_row(contents.len() + 3, contents);
        assert_eq!((col, row), (31, 1));
    }
}
