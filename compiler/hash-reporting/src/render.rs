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
    iter::{once, repeat_n},
};

use hash_source::{
    Source, SourceMapUtils,
    location::{RowColRange, Span},
};
use hash_utils::{
    highlight::{Colour, Modifier, highlight},
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

    /// Function which compute the "true" width of a span in a source file. This
    /// means that if the line contains any [combining marks][https://unicode.org/reports/tr15/#Normalization_Forms_Table].
    ///
    /// If any combining marks are encountered, it is assumed that they are not
    /// rendered within the span, and thus they are subtracted from the
    /// total width of the given drawn span.
    ///
    /// More specifically, when the rendering wants to draw a reference on a
    /// span which will be of some "width", it will use this function to
    /// compute the "true" width of the span, and then draw the span using
    /// the computed width. For example, this snippet of code:
    ///
    /// ```
    /// 'ä' // a + combining diaeresis'
    /// ```
    ///
    /// In this snippet, the compiler lexer will emit an error on the `ä`
    /// character because it is not normalised. The compiler will then want
    /// to draw a span on the `'ä'` character to indicate that it is the
    /// source of the error. However, the `'ä'` character is actually
    /// two characters, the `a` and the combining diaeresis. So, when the
    /// compiler wants to draw the following (snippet 1):
    /// ```
    /// 'ä'
    /// ^^^
    /// ```
    ///
    /// It will actually draw the following (snippet 2):
    ///
    /// ```
    /// 'ä'
    /// ^^^^
    /// ```
    ///
    /// To solve this issue, we need to compute the "true" width of the span,
    /// which is the width of the span minus the number of combining marks
    /// in the span. So, in the above example, the "true" width of the span
    /// is 3, and thus the compiler will draw (snippet 1) instead of
    /// (snippet 2).
    ///
    /// N.B. It is assumed that the provided [RowColRange] references on the
    /// `line`.
    fn get_line_display_width(&self, line: &str, start: usize, end: usize) -> usize {
        // count the number of combining marks is up to the given `end.column`.
        let mut combining_marks = 0;

        for (index, ch) in line.chars().enumerate().skip(start) {
            // Stop counting the characters once we reach the end of the span.
            if index == end {
                break;
            }

            // If it is a combining mark, its not going to be rendered within the
            // span, so we need to subtract it from the total width.
            //
            // @@Investigate: maybe use `unicode-width` here?
            if unicode_normalization::char::is_combining_mark(ch) {
                combining_marks += 1;
            }
        }

        (end - start).saturating_sub(combining_marks)
    }

    /// Function which is responsible for rendering the span note which is
    /// present at the end of the span view. This will print the initial
    /// prefix to the span view, usually the highlighted part of the span,
    /// and then the message.
    ///
    /// This function will automatically format the message to correctly align
    /// all of the lines of the span message with the correct indentation.
    fn render_span_label(
        &self,
        f: &mut fmt::Formatter,
        offset: usize,
        initial_prefix: String,
        longest_indent_width: usize,
        kind: ReportKind,
    ) -> fmt::Result {
        let mut write_line = |line: &str| {
            writeln!(
                f,
                "{} {} {}",
                " ".repeat(longest_indent_width),
                highlight(Colour::Blue, "|"),
                highlight(kind.as_colour(), line)
            )
        };

        let line_count = self.code_message.lines().count();

        // If the number of lines is zero, then we still want to print
        // the initial prefix.
        if line_count == 0 {
            let line: String = once(initial_prefix.as_str())
                .chain(once(" "))
                .chain(once(self.code_message.as_str()))
                .collect();
            return write_line(&line);
        }

        for (index, line) in self.code_message.lines().enumerate() {
            let message_line: String = if index == 0 {
                once(initial_prefix.as_str()).chain(once(" ")).chain(once(line)).collect()
            } else {
                repeat_n(" ", offset).chain(once(line)).collect()
            };

            write_line(&message_line)?;
        }

        Ok(())
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

            // Print the line number and the line
            writeln!(f, "{line_number} {}   {line}", highlight(Colour::Blue, "|"))?;

            // If this is the error view. then we want to print the
            // the span label.
            if index == start_row && !line.is_empty() {
                let dashes_length = self.get_line_display_width(line, start_column, end_column);
                let dashes: String = repeat_n(LINE_DIAGNOSTIC_MARKER, dashes_length).collect();

                let highlight_offset = self.get_line_display_width(line, 0, start_column) + 2;

                // Offset of the initial space between the start, then the dashes, then a space
                let total_offset = highlight_offset + dashes_length + 1;

                let initial_prefix =
                    repeat_n(" ", highlight_offset).chain(once(dashes.as_str())).collect();

                self.render_span_label(
                    f,
                    total_offset,
                    initial_prefix,
                    longest_indent_width,
                    kind,
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
        kind: ReportKind,
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
                highlight(kind.as_colour(), &index_str)
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
                        highlight(kind.as_colour(), range_line_number),
                        highlight(kind.as_colour(), connector),
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
                highlight(kind.as_colour(), connector),
                line
            )?;

            // If this is th first row of the diagnostic span, then we want to draw an arrow
            // leading up to it
            if index == start_row {
                // compute the actual length of the arrow
                let arrow_length = self.get_line_display_width(line, 0, start_column + 2);
                let arrow: String =
                    repeat_n('_', arrow_length).chain(once(BLOCK_DIAGNOSTIC_MARKER)).collect();

                writeln!(
                    f,
                    "{} {}  {}",
                    " ".repeat(longest_indent_width),
                    highlight(Colour::Blue, "|"),
                    highlight(kind.as_colour(), arrow)
                )?;
            }

            // Now we perform the same operator for creating an arrow to join the end span,
            // and of course we write the note at the end of the span.
            if index == end_row {
                // compute the actual length of the arrow
                let arrow_length = self.get_line_display_width(line, 0, end_column + 1);
                let arrow: String = once('|')
                    .chain(repeat_n('_', arrow_length))
                    .chain(format!("{BLOCK_DIAGNOSTIC_MARKER}").chars())
                    .collect();

                self.render_span_label(f, arrow_length, arrow, longest_indent_width, kind)?;
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
                    format!("{}:{}", source.canonicalised_path().display(), span.start),
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
