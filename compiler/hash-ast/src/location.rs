//! Frontend-agnostic token/input locations utilities and definitions.
//
// All rights reserved 2021 (c) The Hash Language authors
use crate::module::ModuleIdx;
use std::{convert::TryInto, fmt};

/// Enum representing a location of a token within the source.
///
/// The first element of the tuple represents the line number of the locations
/// and the second element rerpresents the row number.
#[derive(Debug, Eq, Hash, Clone, Copy, PartialEq)]
pub struct Location(u32, u32);

/// General functions to create [Location] variants
impl Location {
    /// Create a 'Pos' variant by providing a single position
    pub fn pos(pos: usize) -> Self {
        Location(pos.try_into().unwrap(), 0)
    }

    /// Create a 'Span' variant by providing a single position and the span of the input token
    pub fn span(start: usize, end: usize) -> Self {
        Location(start.try_into().unwrap(), end.try_into().unwrap())
    }

    /// This function is used to join a location to another. The assumption is made that the left hand-side
    /// span ends before the start of the right hand side span. If that is the case, then a new location is
    /// created with start pos of the lhs, and the end position of the rhs. If that is not the case, the
    /// lhs span is returned.
    ///
    /// In essense, if this was the source stream:
    /// > --------------------------------------------------------------
    /// >  ( <- lhs-start    lhs-end -> )   ( <- rhs-start rhs-end -> )
    /// > --------------------------------------------------------------
    ///
    /// Then the two locations are joined into one, otherwise the lhs is returned
    pub fn join(&self, end: Self) -> Self {
        if self.end() < end.start() {
            return Location::span(self.start(), end.end());
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
}

/// Implementation for displaying a [Location]
impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.0, self.1)
    }
}

#[derive(Debug, Clone)]
pub struct SourceLocation {
    pub location: Location,
    pub module_index: ModuleIdx,
}

impl SourceLocation {
    pub fn interactive() -> Self {
        Self {
            location: Location::pos(0),
            module_index: ModuleIdx(0),
        }
    }
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}: mod={}", self.location, self.module_index.0)
    }
}
