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

/// Convert a [pest::error::InputLocation] into a [Location]
impl From<pest::error::InputLocation> for Location {
    fn from(pest: pest::error::InputLocation) -> Location {
        match pest {
            pest::error::InputLocation::Pos(pos) => Location::Pos(pos), // we could just use Location::Span(pos, 1) here
            pest::error::InputLocation::Span((start, end)) => Location::Span(start, end),
        }
    }
}

/// Convert a [pest::Position] into a [Location]
impl<'a> From<pest::Position<'_>> for Location {
    fn from(pest: pest::Position<'_>) -> Location {
        Location::Pos(pest.pos())
    }
}

/// Convert a [pest::Span] into a [Location]
impl<'a> From<pest::Span<'_>> for Location {
    fn from(pest: pest::Span<'_>) -> Location {
        Location::Span(pest.start(), pest.end())
    }
}

/// Implementation for converting a [pest::iterators::Pair] into a [Location]
impl<'a> From<pest::iterators::Pair<'_, Rule>> for Location {
    fn from(pair: pest::iterators::Pair<'_, Rule>) -> Location {
        Location::from(pair.as_span())
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
