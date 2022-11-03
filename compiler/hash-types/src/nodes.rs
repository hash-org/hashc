//! Storage that holds type information about AST nodes.

use std::ops::BitAnd;

use hash_ast::ast::AstNodeId;
use hash_utils::{new_partial_store, store::PartialStore};

use super::{pats::PatId, terms::TermId};
use crate::scope::ScopeId;

/// Enumerates all the possible informational data that can be associated with
/// an AST node.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NodeInfoTarget {
    /// The node corresponds to the term with the given [`TermId`].
    term: Option<TermId>,
    /// The node corresponds to the pattern with the given [`PatId`].
    pat: Option<PatId>,
    /// The node corresponds to the scope with the given [`ScopeId`].
    scope: Option<ScopeId>,
}

impl NodeInfoTarget {
    /// Asserts that this node info target is a term, and returns its
    /// [`TermId`].
    pub fn term_id(self) -> TermId {
        self.term.expect("expected associated term")
    }

    /// Asserts that this node info target is a pattern, and returns its
    /// [`PatId`].
    pub fn pat_id(self) -> PatId {
        self.pat.expect("expected associated pattern")
    }

    /// Asserts that this node info target is a scope, and returns its
    /// [`ScopeId`].
    pub fn scope_id(self) -> ScopeId {
        self.scope.expect("expected associated scope")
    }

    /// Set the [TermId] of this node info target.
    pub fn set_term_id(&mut self, term_id: TermId) {
        self.term = Some(term_id);
    }

    /// Set the [PatId] of this node info target.
    pub fn set_pat_id(&mut self, pat_id: PatId) {
        self.pat = Some(pat_id);
    }

    /// Set the [ScopeId] of this node info target.
    pub fn set_scope_id(&mut self, scope_id: ScopeId) {
        self.scope = Some(scope_id);
    }
}

impl BitAnd for NodeInfoTarget {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self {
            term: self.term.and(rhs.term),
            pat: self.pat.and(rhs.pat),
            scope: self.scope.and(rhs.scope),
        }
    }
}

impl From<TermId> for NodeInfoTarget {
    fn from(term: TermId) -> Self {
        NodeInfoTarget { term: Some(term), pat: None, scope: None }
    }
}

impl From<PatId> for NodeInfoTarget {
    fn from(pat: PatId) -> Self {
        NodeInfoTarget { term: None, pat: Some(pat), scope: None }
    }
}

impl From<ScopeId> for NodeInfoTarget {
    fn from(scope: ScopeId) -> Self {
        NodeInfoTarget { term: None, pat: None, scope: Some(scope) }
    }
}

new_partial_store!(pub NodeInfoStore<AstNodeId, NodeInfoTarget>);

impl NodeInfoStore {
    /// Update an entry with the associated [AstNodeId] and merge it
    /// with the provided [NodeInfoTarget].
    pub fn update_or_insert(&self, id: AstNodeId, target: NodeInfoTarget) {
        // First check if the entry already exists.
        if self.has(id) {
            self.modify_fast(id, |entry| entry.unwrap().bitand(target));
        } else {
            self.insert(id, target);
        }
    }
}
