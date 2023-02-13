//! Definitions related to control flow.

use core::fmt;

use hash_utils::{
    new_sequence_store_key,
    store::{DefaultSequenceStore, SequenceStore},
};
use textwrap::indent;

use super::{
    environment::env::{AccessToEnv, WithEnv},
    pats::{PatId, PatListId},
    scopes::{StackId, StackIndices},
    utils::common::CommonUtils,
};
use crate::{scopes::BlockTerm, terms::TermId};

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
/// There is a subject, and set of cases.
#[derive(Debug, Clone, Copy)]
pub struct MatchTerm {
    pub subject: TermId,
    pub cases: MatchCasesId,
}

/// A single case in a match term.
///
/// Contains a pattern, a range of stack indices for the binds of the pattern,
/// and a value, similar to `DeclTerm`.
#[derive(Debug, Clone, Copy)]
pub struct MatchCase {
    pub bind_pat: PatId,
    pub stack_id: StackId,
    pub stack_indices: StackIndices,
    pub value: TermId,
}

new_sequence_store_key!(pub MatchCasesId);
pub type MatchCasesStore = DefaultSequenceStore<MatchCasesId, MatchCase>;

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
        writeln!(f, "match {} {{", self.env().with(self.value.subject))?;
        write!(f, "{}", self.env().with(self.value.cases))?;
        write!(f, "}}")?;
        Ok(())
    }
}

impl fmt::Display for WithEnv<'_, MatchCasesId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().match_cases().map_fast(self.value, |cases| {
            for case in cases {
                write!(f, "{}", self.env().with(case))?;
            }
            Ok(())
        })
    }
}

impl fmt::Display for WithEnv<'_, &MatchCase> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let case = format!(
            "{} => {};\n",
            self.env().with(self.value.bind_pat),
            self.env().with(self.value.value)
        );
        let lines = indent(&case, "  ");
        write!(f, "{lines}")?;
        Ok(())
    }
}

impl fmt::Display for WithEnv<'_, &ReturnTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.term_is_void(self.value.expression) {
            write!(f, "return")
        } else {
            write!(f, "return {}", self.env().with(self.value.expression))
        }
    }
}

impl fmt::Display for WithEnv<'_, &LoopControlTerm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            LoopControlTerm::Break => write!(f, "break"),
            LoopControlTerm::Continue => write!(f, "continue"),
        }
    }
}

impl fmt::Display for WithEnv<'_, &IfPat> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} if {}",
            self.env().with(self.value.pat),
            self.env().with(self.value.condition)
        )
    }
}

impl fmt::Display for WithEnv<'_, &OrPat> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().pat_list().map_fast(self.value.alternatives, |alternatives| {
            let mut first = true;
            for pat in alternatives {
                if !first {
                    write!(f, " | ")?;
                }
                write!(f, "{}", self.env().with(*pat))?;
                first = false;
            }
            Ok(())
        })
    }
}
