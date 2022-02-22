//! All rights reserved 2022 (c) The Hash Language authors
use std::fmt;

/// This is used within error messages, so it is formatted in a pretty way to display the expected token kinds
/// after a particular token. This is useful for constructing re-usable error messages that might appear in multiple
/// places when parsing. We use conjunctives to display multiple variants together, so they are readable. If the
/// length of the vector kind is one, we don't use conjunctives to glue kinds together.
pub struct SequenceDisplay<'a, T: 'a>(pub &'a [T]);

impl<'a, T: fmt::Display + 'a> fmt::Display for SequenceDisplay<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0.len() {
            0 => write!(f, ""),
            1 => write!(f, "a '{}'", self.0.get(0).unwrap()),
            _ => {
                let len = self.0.len();
                let mut items = self.0.iter().peekable();

                write!(f, "either a ")?;
                let mut count = 0;

                while let Some(item) = items.next() {
                    if items.peek().is_some() {
                        if count == len - 2 {
                            write!(f, "'{}', or ", item)?;
                        } else {
                            write!(f, "'{}', ", item)?;
                        }
                    } else {
                        write!(f, "'{}'", item)?;
                    };
                    count += 1;
                }

                write!(f, ".")
            }
        }
    }
}
