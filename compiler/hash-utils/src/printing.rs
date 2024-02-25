//! Utilities for printing various data structures that might be used for
//! debugging purposes or for creating human readable error messages when
//! reporting errors.
use std::fmt;

/// This is used a wrapper around [`writeln!`] which integrates writing
/// to a specified stream.
///
/// This macro conveniently unwraps the result of the write operation.
#[macro_export]
macro_rules! stream_writeln {
    ($stream:expr, $($arg:tt)*) => {
        writeln!($stream, $($arg)*).unwrap()
    };
    ($stream:expr) => {
        writeln!($stream).unwrap()
    };

}

/// This is used a wrapper around [`write!`] which integrates writing
/// to a specified stream.
///
/// This macro conveniently unwraps the result of the write operation.
#[macro_export]
macro_rules! stream_write {
    ($stream:expr, $($arg:tt)*) => {
        write!($stream, $($arg)*).unwrap()
    };
    ($stream:expr) => {
        write!($stream).unwrap()
    };

}

/// This is used a wrapper around [`println!`] in order to denote that
/// we don't care about the capturing of the output for testing purposes.
#[macro_export]
macro_rules! stream_less_writeln {
    ($($arg:tt)*) => {
        println!($($arg)*);
    };
}

/// This is used a wrapper around [`eprintln!`] in order to denote that
/// we don't care about the capturing of the output for testing purposes.
#[macro_export]
macro_rules! stream_less_ewriteln {
    ($($arg:tt)*) => {
        eprintln!($($arg)*);
    };
}

#[macro_export]
macro_rules! pluralise {
    ($x:expr) => {
        if $x != 1 {
            "s"
        } else {
            ""
        }
    };
    ("is", $x:expr) => {
        if $x == 1 {
            "is"
        } else {
            "are"
        }
    };
    ("was", $x:expr) => {
        if $x == 1 {
            "was"
        } else {
            "were"
        }
    };
    ("this", $x:expr) => {
        if $x == 1 {
            "this"
        } else {
            "these"
        }
    };
}

/// The [SequenceJoinMode] represents an options list for how a
/// [SequenceDisplay] should be phrased as. The phrasing specifically affects
/// the relationship the items have to one another in the current context. It
/// could be that either one of the items is desired, or if all of the items are
/// desired.
#[derive(Eq, PartialEq)]
pub enum SequenceJoinMode {
    /// Items within a [SequenceDisplay] are phrased as all being options
    Either,
    /// Items within a [SequenceDisplay] are phrased as all being required
    All,
}

impl SequenceJoinMode {
    pub fn as_conjunctive(&self) -> &str {
        match self {
            SequenceJoinMode::Either => "or",
            SequenceJoinMode::All => "and",
        }
    }
}

pub struct SequenceDisplayOptions {
    /// Whether this is specifying that *all* elements are applicable, or *any*
    /// element is applicable.
    pub mode: SequenceJoinMode,

    /// Limit the number of element printed when displaying sequence...
    pub limit: Option<usize>,

    /// Whether items inside should be quoted with backticks.
    pub quote: bool,
}

impl Default for SequenceDisplayOptions {
    fn default() -> Self {
        SequenceDisplayOptions { mode: SequenceJoinMode::Either, limit: None, quote: true }
    }
}

impl SequenceDisplayOptions {
    /// Create a [SequenceDisplayOptions] with no limit and a specified
    /// `joining` mode.
    pub fn new(mode: SequenceJoinMode) -> Self {
        SequenceDisplayOptions { mode, limit: None, quote: true }
    }

    /// Create a [SequenceDisplayOptions] with a specified limit and a specified
    /// `joining` mode.
    pub fn with_limit(mode: SequenceJoinMode, limit: usize) -> Self {
        SequenceDisplayOptions { mode, limit: Some(limit), quote: true }
    }
}

/// This is used within error messages, so it is formatted in a pretty way to
/// display the expected token kinds after a particular token. This is useful
/// for constructing re-usable error messages that might appear in multiple
/// places when parsing. We use conjunctives to display multiple variants
/// together, so they are readable. If the length of the vector kind is one, we
/// don't use conjunctives to glue kinds together.
pub struct SequenceDisplay<'a, T: 'a> {
    /// The items that the display will show
    pub items: &'a [T],

    /// Options on how to print the sequence display
    pub options: SequenceDisplayOptions,
}

impl<'a, T: 'a> SequenceDisplay<'a, T> {
    /// Create a new [SequenceDisplay]
    pub fn new(items: &'a [T], options: SequenceDisplayOptions) -> Self {
        Self { items, options }
    }

    /// Create a [SequenceDisplay] with the join mode as
    /// [SequenceJoinMode::Either].
    pub fn either(items: &'a [T]) -> Self {
        Self {
            items,
            options: SequenceDisplayOptions {
                mode: SequenceJoinMode::Either,
                ..Default::default()
            },
        }
    }

    /// Create a [SequenceDisplay] with the join mode as
    /// [SequenceJoinMode::All].
    pub fn all(items: &'a [T]) -> Self {
        Self {
            items,
            options: SequenceDisplayOptions { mode: SequenceJoinMode::All, ..Default::default() },
        }
    }
}

impl<'a, T: fmt::Display + 'a> fmt::Display for SequenceDisplay<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let quote = if self.options.quote { "`" } else { "" };

        match self.items.len() {
            0 => write!(f, ""),
            1 if self.options.mode == SequenceJoinMode::Either => {
                write!(f, "a {quote}{}{quote}", self.items.first().unwrap())
            }
            1 => {
                write!(f, "{quote}{}{quote}", self.items.first().unwrap())
            }
            _ => {
                // We essentially want to limit the number of elements to print
                // if the `limit` has been reached or surpassed.
                let (len, overflow) = if let Some(limit) = self.options.limit {
                    if limit >= self.items.len() {
                        (self.items.len(), false)
                    } else {
                        (limit, true)
                    }
                } else {
                    (self.items.len(), false)
                };

                let mut items = self.items[0..len].iter().peekable();

                // We only add the prefix `either a` on `Either` join kind...
                if self.options.mode == SequenceJoinMode::Either {
                    write!(f, "either ")?;
                }

                let mut count = 0;

                while let Some(item) = items.next() {
                    if items.peek().is_some() {
                        if count == len - 2 && !overflow {
                            write!(
                                f,
                                "{quote}{item}{quote}, {} ",
                                self.options.mode.as_conjunctive()
                            )?;
                        } else {
                            write!(f, "{quote}{item}{quote}, ")?;
                        }
                    } else {
                        write!(f, "{quote}{item}{quote}")?;
                    };
                    count += 1;
                }

                // If we overflowed, and the limit is specified then we will
                // print the specified number of missing variants
                if self.options.limit.is_some() && overflow {
                    let count = self.items.len() - self.options.limit.unwrap();
                    write!(f, " {} {count} more", self.options.mode.as_conjunctive())?;
                }

                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sequence_display_tests() {
        let items = ["apple", "cake", "pear"];

        // Test basic join capabilities
        assert_eq!(
            "either `apple`, `cake`, or `pear`",
            format!("{}", SequenceDisplay::either(&items))
        );
        assert_eq!("`apple`, `cake`, and `pear`", format!("{}", SequenceDisplay::all(&items)));
    }

    #[test]
    fn sequence_display_with_limits_tests() {
        let items = ["apple", "cake", "pear", "cider", "steak", "onion"];

        // Test cases where limit should cut off items
        assert_eq!(
            "either `apple`, `cake` or 4 more",
            format!(
                "{}",
                SequenceDisplay::new(
                    &items,
                    SequenceDisplayOptions::with_limit(SequenceJoinMode::Either, 2)
                )
            )
        );
        assert_eq!(
            "`apple`, `cake`, `pear` and 3 more",
            format!(
                "{}",
                SequenceDisplay::new(
                    &items,
                    SequenceDisplayOptions::with_limit(SequenceJoinMode::All, 3)
                )
            )
        );

        // Test limit doesn't cap items
        assert_eq!(
            "`apple`, `cake`, `pear`, `cider`, `steak`, and `onion`",
            format!(
                "{}",
                SequenceDisplay::new(
                    &items,
                    SequenceDisplayOptions::with_limit(SequenceJoinMode::All, 12)
                )
            )
        );

        // Test that `limit` doesn't break when it is set to the same as the length of
        // the list
        let items = ["apple", "orange"];
        assert_eq!(
            "either `apple`, or `orange`",
            format!(
                "{}",
                SequenceDisplay::new(
                    &items,
                    SequenceDisplayOptions::with_limit(SequenceJoinMode::Either, 2)
                )
            )
        );
    }
}
