//! Contains structures that store information about the scopes in a given
//! module, as well as the symbols in each scope.
use super::primitives::{Scope, ScopeId};
use slotmap::SlotMap;

/// Stores all the scopes within a typechecking cycle.
///
/// Scopes are accessed by an ID, of scope [ScopeId].
#[derive(Debug, Default)]
pub struct ScopeStore {
    data: SlotMap<ScopeId, Scope>,
}

impl ScopeStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a scope, returning its assigned [ScopeId].
    pub fn create(&mut self, ty: Scope) -> ScopeId {
        self.data.insert(ty)
    }

    /// Get a scope by [ScopeId].
    ///
    /// If the scope is not found, this function will panic. However, this
    /// shouldn't happen because the only way to acquire a scope is to use
    /// [Self::create], and scopes cannot be deleted.
    pub fn get(&self, ty_id: ScopeId) -> &Scope {
        self.data.get(ty_id).unwrap()
    }

    /// Get a scope by [ScopeId], mutably.
    ///
    /// If the scope is not found, this function will panic.
    pub fn get_mut(&mut self, ty_id: ScopeId) -> &mut Scope {
        self.data.get_mut(ty_id).unwrap()
    }
}

/// Stores a collection of scopes, used from within
/// [LocalStorage](crate::storage::LocalStorage).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopeStack {
    scopes: Vec<ScopeId>,
}

impl ScopeStack {
    /// Create a [ScopeStack] from a single scope.
    pub fn singular(scope_id: ScopeId) -> Self {
        Self {
            scopes: vec![scope_id],
        }
    }

    /// Create a [ScopeStack] from a collection of scopes.
    pub fn many(scopes: impl IntoIterator<Item = ScopeId>) -> Self {
        Self {
            scopes: scopes.into_iter().collect(),
        }
    }

    /// Append a scope to the stack.
    pub fn append(&mut self, scope_id: ScopeId) {
        self.scopes.push(scope_id);
    }

    /// Get the current scope ID.
    pub fn current_scope(&self) -> ScopeId {
        *self.scopes.last().unwrap()
    }

    /// Iterate up the scopes in the stack.
    pub fn iter_up(&self) -> impl Iterator<Item = ScopeId> + '_ {
        self.scopes.iter().copied().rev()
    }

    /// Pop the current scope.
    pub fn pop_scope(&mut self) -> ScopeId {
        // Don't include the first element (root scope).
        if self.scopes.len() <= 1 {
            panic!("Cannot pop root scope")
        } else {
            self.scopes.pop().unwrap()
        }
    }
}
