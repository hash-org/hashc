use crate::grammar::Rule;
use std::fmt;

#[derive(Debug, Eq, Clone, PartialEq)]
pub enum Location {
    Pos(usize),
    Span(usize, usize),
}

impl Location {
    pub fn pos(pos: usize) -> Location {
        Location::Pos(pos)
    }

    pub fn span(start: usize, end: usize) -> Location {
        Location::Span(start, end)
    }
}

impl From<pest::error::InputLocation> for Location {
    fn from(pest: pest::error::InputLocation) -> Location {
        match pest {
            pest::error::InputLocation::Pos(pos) => Location::Pos(pos),
            pest::error::InputLocation::Span((start, end)) => Location::Span(start, end),
        }
    }
}

impl<'a> From<pest::Position<'a>> for Location {
    fn from(pest: pest::Position<'a>) -> Location {
        Location::Pos(pest.pos())
    }
}

impl<'a> From<pest::Span<'a>> for Location {
    fn from(pest: pest::Span<'a>) -> Location {
        Location::Span(pest.start(), pest.end())
    }
}

impl<'a> From<pest::iterators::Pair<'a, Rule>> for Location {
    fn from(pair: pest::iterators::Pair<'a, Rule>) -> Location {
        Location::from(pair.as_span())
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Location::Pos(pos) => write!(f, "{}", pos),
            Location::Span(start, end) => write!(f, "{}:{}", start, end),
        }
    }
}
