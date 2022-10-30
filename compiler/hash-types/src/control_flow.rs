use crate::{
    scope::BlockTerm,
    terms::{TermId, TermListId},
};

/// A loop term.
///
/// Contains a block.
#[derive(Debug, Clone, Copy)]
pub struct LoopTerm {
    pub block: BlockTerm,
}

/// A match term.
///
/// This is the primitive of the pattern matching system.
///
/// There are a set of case patterns, as well as a set of decisions.
/// `decision[i]` is parametrised by the binds in `cases[i]`.
#[derive(Debug, Clone, Copy)]
pub struct MatchTerm {
    // cases: PatListId,
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
