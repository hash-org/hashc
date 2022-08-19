//! Hash Compiler source locations utilities and definitions.
use std::{convert::TryInto, fmt};

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
