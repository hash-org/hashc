//! Frontend-agnostic token/input locations utilities and definitions.
//
// All rights reserved 2021 (c) The Hash Language authors
use std::{convert::TryInto, fmt};

/// Enum representing a location of a token within the source.
#[derive(Debug, Eq, Hash, Clone, Copy, PartialEq)]
pub struct Location(u32, u32);

/// General functions to create [Location] variants
impl Location {
    /// Create a 'Pos' variant by providing a single position
    pub fn pos(pos: usize) -> Location {
        Location(pos.try_into().unwrap(), (pos + 1).try_into().unwrap())
    }

    /// Create a 'Span' variant by providing a single position and the span of the input token
    pub fn span(start: usize, end: usize) -> Location {
        Location(start.try_into().unwrap(), end.try_into().unwrap())
    }

    pub fn start(&self) -> usize {
        self.0.try_into().unwrap()
    }

    pub fn end(&self) -> usize {
        self.1.try_into().unwrap()
    }
}

/// Implementation for displaying a [Location]
impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.0, self.1)
    }
}
