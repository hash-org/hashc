//! Definitions related to control flow.

use core::fmt;

use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey};

use super::{
    environment::env::{AccessToEnv, WithEnv},
    pats::{PatId, PatListId},
    terms::Term,
};
use crate::new::{
    scopes::BlockTerm,
    terms::{TermId, TermListId},
};

/// A loop term.
///
/// Contains a block.
///
/// The type of a loop is `void`, unless it can be proven to never terminate (in
/// which case it is `never`).
#[derive(Debug, Clone, Copy)]
pub struct LoopTerm {
    pub block: BlockTerm,
}

/// A match term.
///
/// This is the primitive of the pattern matching system.
///
/// There is a subject, a set of case patterns, as well as a set of decisions.
/// `decisions[i]` is parametrised by the binds in `cases[i]`.
///
/// This corresponds to `match subject { cases[1] => decisions[1],...,cases[n]
/// => decisions[n] }`.
///
/// It is an invariant that `cases.len() == decisions.len()`.
#[derive(Debug, Clone, Copy)]
pub struct MatchTerm {
    pub subject: TermId,
    pub cases: PatListId,
    pub decisions: TermListId,
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

/// A term relating to loop control flow.
///
/// Either break or continue.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopControlTerm {
    Break,
    Continue,
}

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

impl fmt::Display for WithEnv<'_, &LoopTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "loop {}", self.env().with(&self.value.block))
    }
}

impl fmt::Display for WithEnv<'_, &MatchTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "match {{")?;
        for index in self.value.cases.to_index_range() {
            let pat = self.stores().pat_list().get_at_index(self.value.cases, index);
            let term = self.stores().term_list().get_at_index(self.value.decisions, index);
            let term_str = self.env().with(term).to_string();
            let term_lines = term_str.lines();

            let mut first = true;
            for line in term_lines {
                if first {
                    write!(f, "{} => {}", self.env().with(pat), line)?;
                    first = false;
                } else {
                    write!(f, "  {}", line)?;
                }
            }
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl fmt::Display for WithEnv<'_, &ReturnTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.classifier().term_is_void(self.value.expression) {
            write!(f, "return")
        } else {
            write!(f, "return {}", self.env().with(self.value.expression))
        }
    }
}
