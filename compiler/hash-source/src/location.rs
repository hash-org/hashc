//! Hash Compiler source locations utilities and definitions.
use std::{
    convert::TryInto,
    fmt::{self, Display},
};

use derive_more::Constructor;

use crate::SourceId;

/// [Span] represents a location of a range of tokens within the source.
///
/// The first element of the tuple represents the starting byte offset and the
/// second element represents the ending byte offset.
#[derive(Debug, Eq, Hash, Clone, Copy, PartialEq)]
pub struct Span(u32, u32);

impl Span {
    /// Create a [Span] by providing a start and end byte position.
    pub fn new(start: usize, end: usize) -> Self {
        debug_assert!(
            end >= start,
            "Got invalid span for Span::new. Start needs to be smaller than end."
        );

        Span(start.try_into().unwrap(), end.try_into().unwrap())
    }

    /// This function is used to join a [Span] to another [Span]. The assumption
    /// is made that the left hand-side [Span] ends before the start of the
    /// right hand side [Span]. If that is the case, then a new location is
    /// created with start position of the `self`, and the end position of the
    /// `other`. If that is not the case, the `self` span is returned.
    ///
    /// In essence, if this was the source stream:
    /// ```text
    /// --------------------------------------------------------------
    ///  ( <- self.start  self.end -> )   ( <- other.start other.end -> )
    /// --------------------------------------------------------------
    /// ```
    ///
    /// Then the two locations are joined into one, otherwise the lhs is
    /// returned.
    #[must_use]
    pub fn join(&self, other: Self) -> Self {
        if self.end() <= other.start() {
            return Span::new(self.start(), other.end());
        }

        *self
    }

    /// Get the start of the [Span].
    pub fn start(&self) -> usize {
        self.0.try_into().unwrap()
    }

    /// Get the end of the [Span].
    pub fn end(&self) -> usize {
        self.1.try_into().unwrap()
    }

    /// Compute the actual size of the [Span] by subtracting the end from start.
    pub fn len(&self) -> usize {
        self.end() - self.start()
    }

    /// Check if the [Span] is empty.
    pub fn is_empty(&self) -> bool {
        self.start() == self.end()
    }

    /// Convert the [Span] into a [SourceLocation].
    pub fn into_location(self, source_id: SourceId) -> SourceLocation {
        SourceLocation::new(self, source_id)
    }
}

impl Default for Span {
    fn default() -> Self {
        Self::new(0, 0)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.0, self.1)
    }
}

/// A [SourceLocation] describes the location of something that is relative to
/// a module that is within the workspace and that has an associated [Span].
///
/// [SourceLocation]s are only used when printing reports within the
/// `hash_reporting` crate. Ideally, data structures that need to store
/// locations of various items should use [Span] and then convert into
/// [SourceLocation]s.
#[derive(Debug, Clone, Copy, Constructor, PartialEq, Eq, Hash)]
pub struct SourceLocation {
    /// The associated [Span] with the [SourceLocation].
    pub span: Span,
    /// The id of the source that the span is referencing.
    pub id: SourceId,
}

impl SourceLocation {
    /// Join the span of a [SourceLocation] with another [SourceLocation].
    ///
    /// *Note*: the `id` of both [SourceLocation]s must be the same.
    pub fn join(self, other: Self) -> Self {
        assert!(self.id == other.id);

        Self { id: self.id, span: self.span.join(other.span) }
    }
}

/// Represents a position within a source using a `row` and `column`  
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct RowCol {
    /// The row number, indexing starts from `0`, but when printed, one is
    /// always added as most editors display rows beginning from `1`.
    pub row: usize,
    /// The column number, indexing starts from `0`, but when printed, one is
    /// always added as most editors display rows beginning from `1`.
    pub column: usize,
}

impl Display for RowCol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.row + 1, self.column + 1)
    }
}

/// [RowColSpan] is a data structure that is equivalent to [Span] but uses rows
/// and columns to denote offsets within the source file. [RowColSpan] is only
/// re-used when specific line numbers need to be reported, this shouldn't be
/// used for general purpose storage of positions of source items.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct RowColSpan {
    /// The starting position of the [RowColSpan].
    pub start: RowCol,
    /// The end position of the [RowColSpan].
    pub end: RowCol,
}

impl RowColSpan {
    /// Create a new [RowColSpan] from a `start` and `end`.
    pub fn new(start: RowCol, end: RowCol) -> Self {
        Self { start, end }
    }

    /// Get the associated rows with the start and end of the [RowColSpan].
    pub fn rows(&self) -> (usize, usize) {
        (self.start.row, self.end.row)
    }

    pub fn columns(&self) -> (usize, usize) {
        (self.start.column, self.end.column)
    }
}

impl Display for RowColSpan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.start == self.end {
            write!(f, "{}", self.start)
        } else {
            write!(f, "{}-{}", self.start, self.end)
        }
    }
}

/// Function to compute a row and column number from a given source string
/// and an offset within the source. This will take into account the number
/// of encountered newlines and characters per line in order to compute
/// precise row and column numbers of the span.
pub fn compute_row_col_from_offset(offset: usize, source: &str, non_inclusive: bool) -> RowCol {
    let source_lines = source.split('\n');

    let mut bytes_skipped = 0;
    let mut total_lines: usize = 0;
    let mut last_line_len = 0;

    let mut line_index = None;
    for (line_idx, line) in source_lines.enumerate() {
        // @@Future: rather than *assuming* that the newline will always be a single
        // byte, we should perform a `normalisation` operation when the source
        // file is first read, so that we can deal with any line ending
        // regardless of the current environment.
        //
        // Add a single byte for the `\n`...
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
            line_index = Some(RowCol { column: offset - bytes_skipped, row: line_idx });
            break;
        }

        bytes_skipped += skip_width;
        total_lines += 1;
        last_line_len = line.len();
    }

    line_index.unwrap_or(RowCol {
        column: last_line_len.saturating_sub(1),
        row: total_lines.saturating_sub(1),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offset_test() {
        let contents = "Hello, world!\nGoodbye, world, it has been fun.";

        let RowCol { column, row } =
            compute_row_col_from_offset(contents.len() - 1, contents, false);
        assert_eq!((column, row), (31, 1));

        let RowCol { column, row } =
            compute_row_col_from_offset(contents.len() + 3, contents, false);
        assert_eq!((column, row), (31, 1));
    }
}
