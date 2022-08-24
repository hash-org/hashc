//! Storage that holds type information about AST nodes.

use hash_ast::ast::AstNodeId;
use hash_utils::new_partial_store;

use super::{pats::PatId, terms::TermId};

/// Enumerates all the possible informational data that can be associated with
/// an AST node.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum NodeInfoTarget {
    /// The node corresponds to the term with the given [`TermId`].
    Term(TermId),
    /// The node corresponds to the pattern with the given [`PatId`].
    Pat(PatId),
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

new_partial_store!(pub NodeInfoStore<AstNodeId, NodeInfoTarget>);
