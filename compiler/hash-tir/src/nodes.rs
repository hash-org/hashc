//! Storage that holds type information about AST nodes.

use hash_ast::ast::AstNodeId;
use hash_utils::{
    new_partial_store,
    store::{FxHashMap, PartialCloneStore, PartialStore},
};

use super::{pats::PatId, terms::TermId};
use crate::scope::ScopeId;

/// Enumerates all the possible informational data that can be associated with
/// an AST node.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NodeInfoTarget {
    /// The node corresponds to the term with the given [`TermId`].
    pub term: Option<TermId>,
    /// The node corresponds to the pattern with the given [`PatId`].
    pub pat: Option<PatId>,
    /// The node corresponds to the scope with the given [`ScopeId`].
    pub scope: Option<ScopeId>,
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

    /// Combine two [`NodeInfoTarget`]s together.
    pub fn combine(self, other: Self) -> Self {
        Self {
            term: self.term.or(other.term),
            pat: self.pat.or(other.pat),
            scope: self.scope.or(other.scope),
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

new_partial_store!(pub InfoStore<AstNodeId, NodeInfoTarget>);

new_partial_store!(pub PatMapping<PatId, AstNodeId>);

#[derive(Debug, Default)]
pub struct NodeInfoStore {
    /// Mapping between [AstNodeId]s and [NodeInfoTarget]s. This store is
    /// partial and many [AstNodeId]s will not have a corresponding
    /// [NodeInfoTarget].
    store: InfoStore,

    /// A mapping between [PatId]s to [AstNodeId]s. This is needed to
    /// lookup the [AstNodeId] of a [PatId] when we need to append additional
    /// information about patterns to the [InfoStore].
    reverse_pat_mapping: PatMapping,
}

impl NodeInfoStore {
    /// Create a new [NodeInfoStore].
    pub fn new() -> Self {
        Self { store: InfoStore::new(), reverse_pat_mapping: PatMapping::new() }
    }

    /// Update an entry with the associated [AstNodeId] and merge it
    /// with the provided [NodeInfoTarget].
    pub fn update_or_insert(&self, id: AstNodeId, target: NodeInfoTarget) {
        // First check if the entry already exists.
        if self.store.has(id) {
            self.store.modify_fast(id, |entry| {
                let entry = entry.unwrap();
                *entry = entry.combine(target);
            });
        } else {
            self.store.insert(id, target);

            if let Some(pat_id) = target.pat {
                self.reverse_pat_mapping.insert(pat_id, id);
            }
        }
    }

    /// Get the [NodeInfoTarget] associated with the given [AstNodeId].
    pub fn pat_to_node_id(&self, pat_id: PatId) -> Option<AstNodeId> {
        self.reverse_pat_mapping.get(pat_id)
    }

    pub fn node_info(&self, id: AstNodeId) -> Option<NodeInfoTarget> {
        self.store.get(id)
    }
}
