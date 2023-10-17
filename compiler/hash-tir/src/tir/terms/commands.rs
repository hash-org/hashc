//! Definitions related to imperative commands.
use std::fmt;

use hash_storage::store::{statics::StoreId, SequenceStoreKey};

use super::{Term, TermId};

/// Assign a value to a subject.
#[derive(Debug, Clone, Copy)]
pub struct AssignTerm {
    // If the subject is assign,
    pub subject: TermId,
    pub value: TermId,
}

impl fmt::Display for AssignTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} = {}", self.subject, self.value)
    }
}

/// A loop term.
///
/// Contains an inner term which should produce side-effects.
///
/// The type of a loop is `void`, unless it can be proven to never terminate (in
/// which case it is `never`).
#[derive(Debug, Clone, Copy)]
pub struct LoopTerm {
    pub inner: TermId,
}

/// A term relating to loop control flow.
///
/// Either break or continue.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopControlTerm {
    Break,
    Continue,
}

/// A return term.
///
/// This is typed as `never`.
#[derive(Debug, Clone, Copy)]
pub struct ReturnTerm {
    // The expression to return. If there is no such expression in the code, then this will be the
    // empty tuple term.
    pub expression: TermId,
}

impl fmt::Display for LoopTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "loop {}", self.inner)
    }
}

impl fmt::Display for ReturnTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if matches!(*self.expression.value(), Term::Tuple(tuple_term) if tuple_term.data.value().is_empty())
        {
            write!(f, "return")
        } else {
            write!(f, "return {}", self.expression)
        }
    }
}

impl fmt::Display for LoopControlTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LoopControlTerm::Break => write!(f, "break"),
            LoopControlTerm::Continue => write!(f, "continue"),
        }
    }
}
