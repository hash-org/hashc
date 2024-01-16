//! Scope data structures for the scope checking pass.
use std::collections::{HashMap, HashSet};

use hash_ast::ast::AstNodeId;
use hash_source::{identifier::Identifier, SourceId};
use hash_utils::fxhash::FxHashMap;

/// The kind of a scope member.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ScopeMemberKind {
    /// A data definition: either a struct or an enum.
    Data,
    /// A constructor (enum variant).
    Constructor,
    /// A function.
    Function,
    /// A module block.
    Module,
    /// A parameter.
    Parameter,
    /// A variable declared on the stack.
    Variable,
}

/// A member of a scope.
#[derive(Debug, Clone)]
pub struct ScopeMember {
    name: Identifier,
    /// The name node which defines this member.
    defined_by: AstNodeId,
    /// The set of name nodes which reference this member.
    referenced_by: HashSet<AstNodeId>,
    /// The kind of this scope member.
    kind: ScopeMemberKind,
    /// The index of this scope member in the scope.
    index_in_scope: usize,
}

impl ScopeMember {
    /// Get the name of this scope member.
    pub(crate) fn name(&self) -> &Identifier {
        &self.name
    }

    /// Get the node which defines this scope member.
    pub(crate) fn defined_by(&self) -> AstNodeId {
        self.defined_by
    }

    /// Whether this scope member is referenced by any other nodes.
    pub(crate) fn is_referenced(&self) -> bool {
        !self.referenced_by.is_empty()
    }

    /// Get the index of this scope member in the scope.
    pub(crate) fn index_in_scope(&self) -> usize {
        self.index_in_scope
    }

    /// Get the kind of this scope member.
    pub(crate) fn kind(&self) -> ScopeMemberKind {
        self.kind
    }

    /// Add a referencing node to this scope member.
    pub(crate) fn add_referencing_node(&mut self, node: AstNodeId) {
        self.referenced_by.insert(node);
    }
}

/// A scope, which contains a set of members indexed by their identifier.
///
/// Scopes also keep track of their parent scope, if they have one.
#[derive(Debug, Clone)]
pub(crate) struct Scope {
    node: AstNodeId,
    members: HashMap<Identifier, ScopeMember>,
    parent: Option<AstNodeId>,
}

impl Scope {
    /// Create a new scope without a parent.
    pub(crate) fn root(node: AstNodeId) -> Self {
        Self { node, members: HashMap::new(), parent: None }
    }

    /// Create a new scope with a parent.
    pub(crate) fn child(node: AstNodeId, parent: AstNodeId) -> Self {
        Self { node, members: HashMap::new(), parent: Some(parent) }
    }

    /// Get the node ID of this scope.
    pub(crate) fn node(&self) -> AstNodeId {
        self.node
    }

    /// Register a member in this scope.
    pub(crate) fn register_member(
        &mut self,
        node_id: AstNodeId,
        ident: Identifier,
        kind: ScopeMemberKind,
    ) {
        let index_in_scope = self.members.len();
        self.members.insert(
            ident,
            ScopeMember {
                name: ident,
                defined_by: node_id,
                referenced_by: HashSet::new(),
                kind,
                index_in_scope,
            },
        );
    }

    /// Get a member from this scope (mutable).
    pub(crate) fn get_member_mut(&mut self, ident: Identifier) -> Option<&mut ScopeMember> {
        self.members.get_mut(&ident)
    }

    /// Get a member from this scope
    pub(crate) fn get_member(&self, ident: Identifier) -> Option<&ScopeMember> {
        self.members.get(&ident)
    }
}

/// The scope data for a single source.
///
/// It contains a record of all the scopes, definitions, and references
/// in the AST, indexed by the AST node ID of each relevant node.
#[derive(Debug, Clone, Default)]
pub struct ScopeData {
    scope_by_node: FxHashMap<AstNodeId, Scope>,
}

impl ScopeData {
    /// Get the scope of a node (mutable).
    pub(crate) fn get_scope_mut(&mut self, node: AstNodeId) -> Option<&mut Scope> {
        self.scope_by_node.get_mut(&node)
    }

    /// Get the scope of a node (mutable), panicking if it does not exist.
    pub(crate) fn get_existing_scope_mut(&mut self, node: AstNodeId) -> &mut Scope {
        self.get_scope_mut(node).unwrap()
    }

    /// Get the scope of a node.
    pub(crate) fn get_scope(&self, node: AstNodeId) -> Option<&Scope> {
        self.scope_by_node.get(&node)
    }

    /// Get the scope of a node, panicking if it does not exist.
    pub(crate) fn get_existing_scope(&self, node: AstNodeId) -> &Scope {
        self.get_scope(node).unwrap()
    }

    /// Insert a scope into the scope data, only if it does not already exist.
    pub(crate) fn insert_scope_if_does_not_exist(
        &mut self,
        node: AstNodeId,
        f: impl FnOnce() -> Scope,
    ) -> &mut Scope {
        self.scope_by_node.entry(node).or_insert_with(f)
    }
}

/// The scope data for all sources.
#[derive(Debug, Clone, Default)]
pub struct AllScopeData {
    data: FxHashMap<SourceId, ScopeData>,
}

impl AllScopeData {
    /// Get the scope data for a source.
    pub fn get_for_source(&mut self, source: SourceId) -> &mut ScopeData {
        self.data.entry(source).or_default()
    }
}
