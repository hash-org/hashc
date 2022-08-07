//! Contains structures that store information about the scopes in a given
//! module, as well as the symbols in each scope.
use std::cell::RefCell;

use hash_utils::{new_store, new_store_key};

use super::primitives::Scope;

new_store_key!(pub ScopeId);
new_store!(pub ScopeStore<ScopeId, Scope>);

/// Stores a collection of scopes, used from within
/// [LocalStorage](crate::storage::LocalStorage).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopeStack {
    scopes: RefCell<Vec<ScopeId>>,
}

impl ScopeStack {
    /// Create a [ScopeStack] from a single scope.
    pub fn singular(scope_id: ScopeId) -> Self {
        Self { scopes: RefCell::new(vec![scope_id]) }
    }

    /// Create a [ScopeStack] from a collection of scopes.
    pub fn many(scopes: impl IntoIterator<Item = ScopeId>) -> Self {
        Self { scopes: RefCell::new(scopes.into_iter().collect()) }
    }

    /// Append a scope to the stack.
    pub fn append(&self, scope_id: ScopeId) {
        self.scopes.borrow_mut().push(scope_id);
    }

    /// Get the current scope ID.
    pub fn current_scope(&self) -> ScopeId {
        *self.scopes.borrow().last().unwrap()
    }

    /// Iterate up the scopes in the stack.
    ///
    /// *Warning*: It is not safe to modify the scope stack by popping scopes
    /// while iterating!
    pub fn iter_up(&self) -> impl Iterator<Item = ScopeId> + DoubleEndedIterator + '_ {
        let len = self.scopes.borrow().len();
        (0..len).map(move |index| *self.scopes.borrow().get(index).unwrap())
    }

    /// Pop the current scope.
    pub fn pop_scope(&self) -> ScopeId {
        let mut scopes = self.scopes.borrow_mut();
        // Don't include the first element (root scope).
        if scopes.len() <= 1 {
            drop(scopes);
            panic!("Cannot pop root scope")
        } else {
            scopes.pop().unwrap()
        }
    }

    /// Pop the given scope.
    ///
    /// Panics if the last scope is not the same as the given ID.
    pub fn pop_the_scope(&self, expected_id: ScopeId) -> ScopeId {
        let popped = self.pop_scope();
        assert!(popped == expected_id, "Expected scope ID {:?} but got {:?}", expected_id, popped);
        popped
    }
}
