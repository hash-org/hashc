//! Frontend-agnostic token/input locations utilities and definitions.
//
// All rights reserved 2021 (c) The Hash Language authors
use std::{convert::TryInto, fmt, path::PathBuf};

/// Enum representing a location of a token within the source.
///
/// The first element of the tuple represents the line number of the locations
/// and the second element rerpresents the row number.
#[derive(Debug, Eq, Hash, Clone, Copy, PartialEq)]
pub struct Location(u32, u32);

/// General functions to create [Location] variants
impl Location {
    /// Create a 'Pos' variant by providing a single position
    pub fn pos(pos: usize) -> Location {
        Location(pos.try_into().unwrap(), 0)
    }

    /// Create a 'Span' variant by providing a single position and the span of the input token
    pub fn span(start: usize, end: usize) -> Location {
        Location(start.try_into().unwrap(), end.try_into().unwrap())
    }

    pub fn row(&self) -> usize {
        self.0.try_into().unwrap()
    }

    pub fn col(&self) -> usize {
        self.1.try_into().unwrap()
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
    pub path: PathBuf,
}

impl SourceLocation {
    pub fn interactive() -> Self {
        Self {
            location: Location::pos(1), // @@Improvement: one, since it's assumed to be first line, however it would be nice if interpreter remembered what line number we're on
            path: "<interactive>".into(),
        }
    }
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}: {}", self.path, self.location)
    }
}
