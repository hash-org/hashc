//! Hash Compiler source locations utilities and definitions.
use std::{
    cmp,
    fmt::{self, Display},
    ops::{Deref, DerefMut},
};

use derive_more::Constructor;
use hash_utils::{
    range_map::RangeMap,
    schemars::{self, JsonSchema},
    serde::{self, Serialize},
};
use line_span::LineSpanExt;

use crate::{SourceId, SourceMapUtils};

/// [ByteRange] represents a location of a range of tokens within the source.
/// The range itself is considered to be inclusive, so ranges such as `0:0`
/// would include the first byte of the source, and ranges like `0:1` would
/// include the first two bytes of the source.
#[derive(Debug, Eq, Hash, Clone, Copy, PartialEq, JsonSchema, Serialize)]
#[serde(crate = "self::serde")]
pub struct ByteRange(u32, u32);

impl ByteRange {
    /// Create a [ByteRange] by providing a start and end byte position.
    pub fn new(start: usize, end: usize) -> Self {
        debug_assert!(end >= start, "invalid span. start > end. start={} end={}", start, end);
        ByteRange(start as u32, end as u32)
    }

    /// Create a single byte [ByteRange] by providing a start position.
    pub fn singleton(start: usize) -> Self {
        ByteRange(start as u32, start as u32)
    }

    /// This function is used to join a [ByteRange] to another [ByteRange].
    /// The assumption is made that the left hand-side [ByteRange] ends before
    /// the start of the right hand side [ByteRange]. If that is the case, then
    /// a new location is created with start position of the `self`, and the
    /// end position of the `other`. If that is not the case, the `self`
    /// span is returned.
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
            return ByteRange::new(self.start(), other.end());
        }

        *self
    }

    /// Get the start of the [ByteRange].
    pub fn start(&self) -> usize {
        self.0.try_into().unwrap()
    }

    /// Get the end of the [ByteRange].
    pub fn end(&self) -> usize {
        self.1.try_into().unwrap()
    }

    /// Compute the actual size of the [ByteRange] by subtracting the end
    /// from start.
    pub fn len(&self) -> usize {
        (self.end() + 1) - self.start()
    }

    /// Check if the [ByteRange] is empty.
    pub fn is_empty(&self) -> bool {
        self.start() == self.end()
    }

    /// Convert the [ByteRange] into a [Span].
    pub fn into_location(self, source_id: SourceId) -> Span {
        Span::new(self, source_id)
    }

    /// Check if one span intersects with another one.
    ///
    /// We check whether the `current` token touches the other token, if it
    /// does, then we consider it to be intersecting.
    /// ```
    /// 
    ///  (current token)
    ///                 (other token)
    /// ```
    #[inline(always)]
    pub fn is_right_before(&self, other: Self) -> bool {
        self.start() == (other.end() + 1)
    }
}

impl Default for ByteRange {
    fn default() -> Self {
        Self::new(0, 0)
    }
}

impl fmt::Display for ByteRange {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.0, self.1)
    }
}

/// A [Span] describes the location of something that is relative to
/// a module that is within the workspace and that has an associated
/// [ByteRange].
///
/// [Span]s are only used when printing reports within the
/// `hash_reporting` crate. Ideally, data structures that need to store
/// locations of various items should use [ByteRange] and then convert into
/// [Span]s.
#[derive(Debug, Clone, Copy, Constructor, PartialEq, Eq, Hash, JsonSchema, Serialize)]
#[serde(crate = "self::serde")]
pub struct Span {
    /// The associated [ByteRange] with the [Span].
    pub range: ByteRange,

    /// The id of the source that the span is referencing.
    pub id: SourceId,
}

impl Span {
    /// Create a null-[Span], setting the range to be 0-0, and
    /// pointing to the prelude module.
    pub fn null() -> Self {
        Self::new(ByteRange::default(), SourceId::default())
    }

    /// Join the span of a [Span] with another [Span].
    ///
    /// *Note*: the `id` of both [Span]s must be the same.
    pub fn join(self, other: Self) -> Self {
        debug_assert!(self.id == other.id);

        Self { id: self.id, range: self.range.join(other.range) }
    }

    /// Get the length of the [Span].
    pub fn len(&self) -> usize {
        self.range.len()
    }

    /// Check if the [Span] is empty.
    pub fn is_empty(&self) -> bool {
        self.range.is_empty()
    }

    /// Format the [ByteRange] into a file path with a column and row number.
    pub fn fmt_range(&self) -> String {
        SourceMapUtils::map(self.id, |source| format!("{}", source.row_cols(self.range)))
    }

    /// Format the [Span] into a file path with a column and row number.
    ///
    /// The span is formatted into the following format:
    /// ```notrust
    /// <path>:<start.row>:<start.column>:<end.row>:<end.column>
    /// ```
    pub fn fmt_path(&self) -> String {
        SourceMapUtils::map(self.id, |source| {
            format!("{}:{}", source.canonicalised_path().display(), source.row_cols(self.range))
        })
    }

    /// Get the contents of the [Span] from the [SpannedSource].
    pub fn contents(&self) -> String {
        SourceMapUtils::map(self.id, |source| source.hunk(self.range).to_string())
    }

    /// Map the contents of the [Span].
    pub fn map_contents<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&str) -> T,
    {
        SourceMapUtils::map(self.id, |source| f(source.hunk(self.range)))
    }
}

/// Represents a position within a source using a `row` and `column`
#[derive(Debug, Clone, Copy, Eq, PartialEq, JsonSchema)]
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

/// [RowColRange] is a data structure that is equivalent to [ByteRange] but uses
/// rows and columns to denote offsets within the source file. [RowColRange] is
/// only re-used when specific line numbers need to be reported, this shouldn't
/// be used for general purpose storage of positions of source items.
#[derive(Debug, Clone, Copy, Eq, PartialEq, JsonSchema)]
pub struct RowColRange {
    /// The starting position of the [RowColRange].
    pub start: RowCol,
    /// The end position of the [RowColRange].
    pub end: RowCol,
}

impl RowColRange {
    /// Create a new [RowColRange] from a `start` and `end`.
    pub fn new(start: RowCol, end: RowCol) -> Self {
        Self { start, end }
    }

    /// Get the associated rows with the start and end of the [RowColRange].
    pub fn rows(&self) -> (usize, usize) {
        (self.start.row, self.end.row)
    }

    pub fn columns(&self) -> (usize, usize) {
        (self.start.column, self.end.column)
    }
}

impl Display for RowColRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.start == self.end {
            write!(f, "{}", self.start)
        } else {
            write!(f, "{}-{}", self.start, self.end)
        }
    }
}

/// A [SpannedSource] is a wrapper around the contents of a source file that
/// is stored in [SourceMap]. It features useful methods for extracting
/// and reading sections of the source by using [Span] or [ByteRange]s.
#[derive(Clone, Copy)]
pub struct SpannedSource<'s>(pub &'s str);

impl<'s> SpannedSource<'s> {
    /// Create a [SpannedSource] from a [String].
    pub fn from_string(s: &'s str) -> Self {
        Self(s)
    }

    /// Get a hunk of the source by the specified [ByteRange].
    pub fn hunk(&self, range: ByteRange) -> &'s str {
        // clamp the end to the `length` of the contents
        let end = cmp::min(self.0.len(), range.end() + 1);
        &self.0[range.start()..end]
    }
}

/// This struct is used a wrapper for a [RangeMap] in order to
/// implement a nice display format, amongst other things.
#[derive(Debug)]
pub struct LineRanges {
    /// The actual line map.
    map: RangeMap<usize, ()>,

    /// The source that the map belongs to.
    source: SourceId,
}

impl LineRanges {
    /// Create a line range from a string slice.
    pub fn new_from_str(source: SourceId, s: &str) -> Self {
        // Pre-allocate the line ranges to a specific size by counting the number of
        // newline characters within the module source.
        let mut map = RangeMap::with_capacity(bytecount::count(s.as_bytes(), b'\n'));

        // Now, iterate through the source and record the position of each newline
        // range, and push it into the map.
        let mut count = 0;

        for span in s.line_spans() {
            map.append(count..=span.end(), ());
            count = span.ending();
        }

        Self { map, source }
    }

    /// Get a [RowCol] from a given byte index.
    pub fn get_row_col(&self, index: usize, end: bool) -> RowCol {
        let ranges = &self.map;
        let line = ranges.index_wrapping(index);
        let key = ranges.key_wrapping(index);
        let offset = key.start();
        let column_byte_offset = index + (end as usize) - offset;

        // Unfortunately, it isn't as simple as just counting the number of
        // bytes from the start of the line to the current byte index, as
        // some characters are encoded using multiple bytes. So, we need to
        // iterate the character indices until we reach the current byte
        // index.
        let mut column = 0;

        SourceMapUtils::map(self.source, |source| {
            let line_range = ByteRange::new(key.start(), key.end());
            let mut indices = source.contents().hunk(line_range).char_indices();

            while let Some((index, _)) = indices.next()
                && index < column_byte_offset
            {
                column += 1;
            }
        });

        RowCol { row: line, column }
    }

    /// Returns the line and column of the given [ByteRange]
    pub fn row_cols(&self, range: ByteRange) -> RowColRange {
        let start = self.get_row_col(range.start(), false);
        let end = self.get_row_col(range.end(), true);

        RowColRange { start, end }
    }
}

impl Deref for LineRanges {
    type Target = RangeMap<usize, ()>;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl DerefMut for LineRanges {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}

impl Display for LineRanges {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, (key, _)) in self.iter().enumerate() {
            writeln!(f, "{key}: {}", index + 1)?;
        }

        Ok(())
    }
}
