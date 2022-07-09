//! Hash utilities for printing various data structures that might be used for
//! debugging purposes or for creating human readable error messages when
//! reporting errors.
use std::fmt;

/// The [SequenceJoinKind] represents an options list for how a
/// [SequenceDisplay] should be phrased as. The phrasing specifically affects
/// the relationship the items have to one another in the current context. It
/// could be that either one of the items is desired, or if all of the items are
/// desired.
#[derive(Eq, PartialEq)]
pub enum SequenceJoinKind {
    /// Items within a [SequenceDisplay] are phrased as all being options
    Either,
    /// Items within a [SequenceDisplay] are phrased as all being required
    All,
}

impl SequenceJoinKind {
    pub fn as_conjunctive(&self) -> &str {
        match self {
            SequenceJoinKind::Either => "or",
            SequenceJoinKind::All => "and",
        }
    }
}

/// This is used within error messages, so it is formatted in a pretty way to
/// display the expected token kinds after a particular token. This is useful
/// for constructing re-usable error messages that might appear in multiple
/// places when parsing. We use conjunctives to display multiple variants
/// together, so they are readable. If the length of the vector kind is one, we
/// don't use conjunctives to glue kinds together.
pub struct SequenceDisplay<'a, T: 'a> {
    pub items: &'a [T],
    mode: SequenceJoinKind,
}

impl<'a, T: 'a> SequenceDisplay<'a, T> {
    /// Create a new [SequenceDisplay]
    pub fn new(items: &'a [T], mode: SequenceJoinKind) -> Self {
        Self { items, mode }
    }

    /// Create a [SequenceDisplay] with the join mode as
    /// [SequenceJoinKind::Either]
    pub fn either(items: &'a [T]) -> Self {
        Self { items, mode: SequenceJoinKind::Either }
    }

    /// Create a [SequenceDisplay] with the join mode as [SequenceJoinKind::All]
    pub fn all(items: &'a [T]) -> Self {
        Self { items, mode: SequenceJoinKind::All }
    }
}

impl<'a, T: fmt::Display + 'a> fmt::Display for SequenceDisplay<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.items.len() {
            0 => write!(f, ""),
            1 if self.mode == SequenceJoinKind::Either => {
                write!(f, "a `{}`", self.items.get(0).unwrap())
            }
            1 => {
                write!(f, "`{}`", self.items.get(0).unwrap())
            }
            _ => {
                let len = self.items.len();
                let mut items = self.items.iter().peekable();

                // We only add the prefix `either a` on `Either` join kind...
                if self.mode == SequenceJoinKind::Either {
                    write!(f, "either a ")?;
                }

                let mut count = 0;

                while let Some(item) = items.next() {
                    if items.peek().is_some() {
                        if count == len - 2 {
                            write!(f, "`{}`, {} ", item, self.mode.as_conjunctive())?;
                        } else {
                            write!(f, "`{}`, ", item)?;
                        }
                    } else {
                        write!(f, "`{}`", item)?;
                    };
                    count += 1;
                }

                Ok(())
            }
        }
    }
}
