//! Storage that holds type information about AST nodes.

use hash_ast::ast::AstNodeId;
use hash_utils::new_partial_store;

use super::{pats::PatId, terms::TermId};
use crate::scope::ScopeId;

/// Enumerates all the possible informational data that can be associated with
/// an AST node.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum NodeInfoTarget {
    /// The node corresponds to the term with the given [`TermId`].
    Term(TermId),
    /// The node corresponds to the pattern with the given [`PatId`].
    Pat(PatId),
    /// The node corresponds to the scope with the given [`ScopeId`].
    Scope(ScopeId),
}

impl NodeInfoTarget {
    /// Asserts that this node info target is a term, and returns its
    /// [`TermId`].
    pub fn term_id(self) -> TermId {
        match self {
            NodeInfoTarget::Term(term_id) => term_id,
            _ => unreachable!(),
        }
    }

    /// Asserts that this node info target is a pattern, and returns its
    /// [`PatId`].
    pub fn pat_id(self) -> PatId {
        match self {
            NodeInfoTarget::Pat(pat_id) => pat_id,
            _ => unreachable!(),
        }
    }

    /// Asserts that this node info target is a scope, and returns its
    /// [`ScopeId`].
    pub fn scope_id(self) -> ScopeId {
        match self {
            NodeInfoTarget::Scope(scope_id) => scope_id,
            _ => unreachable!(),
        }
    }
}

impl From<TermId> for NodeInfoTarget {
    fn from(term: TermId) -> Self {
        Self::Term(term)
    }
}

impl From<PatId> for NodeInfoTarget {
    fn from(pat: PatId) -> Self {
        Self::Pat(pat)
    }
}

impl From<ScopeId> for NodeInfoTarget {
    fn from(scope: ScopeId) -> Self {
        Self::Scope(scope)
    }
}

new_partial_store!(pub NodeInfoStore<AstNodeId, NodeInfoTarget>);
