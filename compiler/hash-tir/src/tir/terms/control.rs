//! Definitions related to control flow.

use core::fmt;
use std::fmt::Debug;

use hash_ast::ast::MatchOrigin;
use hash_storage::store::{TrivialSequenceStoreKey, statics::StoreId};
use textwrap::indent;

use crate::{
    stack::StackId,
    stores::tir_stores,
    tir::{PatId, PatListId, TermId},
    tir_node_sequence_store_direct,
};

/// A match term.
///
/// This is the primitive of the pattern matching system.
///
/// There is a subject, and set of cases.
#[derive(Debug, Clone, Copy)]
pub struct MatchTerm {
    pub subject: TermId,
    pub cases: MatchCasesId,

    /// The origin of the match term, and where it came from, i.e. a `match`
    /// case an `if` block, `while` block, or a `for` loop.
    pub origin: MatchOrigin,
}

/// A single case in a match term.
///
/// Contains a pattern, a range of stack indices for the binds of the pattern,
/// and a value, similar to `DeclTerm`.
#[derive(Debug, Clone, Copy)]
pub struct MatchCase {
    pub bind_pat: PatId,
    pub stack_id: StackId,
    pub value: TermId,
}

tir_node_sequence_store_direct!(MatchCase);

/// A conditional pattern, containing a pattern and an condition.
///
/// This is `A if c` in its most general form, where `A` is a pattern and `c` is
/// a boolean-valued term.
///
/// This pattern matches iff `A` matches and `c` is met.
#[derive(Clone, Debug, Copy)]
pub struct IfPat {
    /// The subject pattern `A`.
    pub pat: PatId,
    /// The condition `c`.
    pub condition: TermId,
}

/// A list of alternative patterns.
///
/// This is `A | B | C | ...` in its most general form, where `A`, `B`, `C`,
/// ..., are patterns.
///
/// This pattern matches iff at least one of the patterns in the sequence
/// matches.
#[derive(Copy, Clone, Debug)]
pub struct OrPat {
    /// The sequence of alternative patterns.
    pub alternatives: PatListId,
}

impl fmt::Display for MatchTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "match {} {{", self.subject)?;
        write!(f, "{}", self.cases)?;
        write!(f, "}}")?;
        Ok(())
    }
}

impl fmt::Display for MatchCasesId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for case in self.iter() {
            write!(f, "{}", case)?;
        }
        Ok(())
    }
}

impl fmt::Display for MatchCaseId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", *self.value())
    }
}

impl fmt::Display for MatchCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let case = format!("{} => {};\n", self.bind_pat, self.value);
        let lines = indent(&case, "  ");
        write!(f, "{lines}")?;
        Ok(())
    }
}

impl fmt::Display for IfPat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} if {}", self.pat, self.condition)
    }
}

impl fmt::Display for OrPat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for pat in self.alternatives.iter() {
            if !first {
                write!(f, " | ")?;
            }
            write!(f, "{}", pat)?;
            first = false;
        }
        Ok(())
    }
}
