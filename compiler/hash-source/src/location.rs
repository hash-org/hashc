//! Hash Compiler source locations utilities and definitions.
use crate::SourceId;
use derive_more::Constructor;
use std::{convert::TryInto, fmt};

/// Enum representing a location of a token within the source.
///
/// The first element of the tuple represents the starting byte offset and the
/// second element represents the ending byte offset.
#[derive(Debug, Eq, Hash, Clone, Copy, PartialEq)]
pub struct Span(u32, u32);

/// General functions to create [Span] variants
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
    /// created with start pos of the lhs, and the end position of the rhs. If
    /// that is not the case, the lhs span is returned.
    ///
    /// In essence, if this was the source stream:
    /// ```text
    /// --------------------------------------------------------------
    ///  ( <- lhs-start    lhs-end -> )   ( <- rhs-start rhs-end -> )
    /// --------------------------------------------------------------
    /// ```
    ///
    /// Then the two locations are joined into one, otherwise the lhs is
    /// returned
    #[must_use]
    pub fn join(&self, end: Self) -> Self {
        if self.end() <= end.start() {
            return Span::new(self.start(), end.end());
        }

        *self
    }

    /// Get the start of the location
    pub fn start(&self) -> usize {
        self.0.try_into().unwrap()
    }

    /// Get the end of the location
    pub fn end(&self) -> usize {
        self.1.try_into().unwrap()
    }

    /// Compute the actual size of the span by subtracting the end from start
    pub fn size(&self) -> usize {
        self.end() - self.start()
    }

    /// Get a dummy [Span] that is used as a default value
    #[inline]
    pub fn dummy() -> Span {
        Span(0, 0)
    }
}

impl Default for Span {
    fn default() -> Self {
        Self::new(0, 1)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.0, self.1)
    }
}

#[derive(Debug, Clone, Copy, Constructor, PartialEq, Eq, Hash)]
pub struct SourceLocation {
    pub span: Span,
    pub source_id: SourceId,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        println!("{:?}", std::mem::size_of::<SourceLocation>());
    }
}
