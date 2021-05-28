//! Frontend-agnostic token/input locations utilities and definitions.
//
// All rights reserved 2021 (c) The Hash Language authors
use crate::grammar::Rule;
use std::fmt;

/// Enum representing a location of a token within the source.
#[derive(Debug, Eq, Hash, Clone, Copy, PartialEq)]
pub enum Location {
    Pos(usize),
    Span(usize, usize),
}

/// General functions to create [Location] variants
impl Location {
    /// Create a 'Pos' variant by providing a single position
    pub fn pos(pos: usize) -> Location {
        Location::Pos(pos)
    }

    /// Create a 'Span' variant by providing a single position and the span of the input token
    pub fn span(start: usize, end: usize) -> Location {
        Location::Span(start, end)
    }
}

/// Implementation for displaying a [Location]
impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Location::Pos(pos) => write!(f, "{}", pos),
            Location::Span(start, end) => write!(f, "{}:{}", start, end),
        }
    }
}
