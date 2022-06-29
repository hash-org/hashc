//! Functionality related to resolving variables in scopes.

use super::AccessToOps;
use crate::{
    diagnostics::error::{TcError, TcResult},
    storage::{
        primitives::{Member, TermId},
        AccessToStorage, StorageRef,
    },
};
use hash_source::identifier::Identifier;

/// Contains actions related to variable resolution.
pub struct ScopeResolver<'gs, 'ls, 'cd> {
    /// Inner storage for global, local and core definitions.
    storage: StorageRef<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for ScopeResolver<'gs, 'ls, 'cd> {
    /// Get the inner storage for resolving.
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> ScopeResolver<'gs, 'ls, 'cd> {
    /// Create a new [ScopeResolver].
    pub fn new(storage: StorageRef<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    /// Function used to resolve a particular [Identifier] within the scope. If
    /// the variable is found, then the [Member] of the scope is returned.
    ///
    /// The [TermId] is used in order to give more information about the
    /// location of the variable in the event that the variable could not be
    /// found in the current scope.
    pub(crate) fn resolve_name_in_scopes(
        &self,
        name: Identifier,
        term: TermId,
    ) -> TcResult<Member> {
        // Here, we have to look in the scopes:
        for scope_id in self.scopes().iter_up() {
            match self.reader().get_scope(scope_id).get(name) {
                // Found in this scope, return the member.
                Some(result) => return Ok(result),
                // Continue to the next (higher) scope:
                None => continue,
            }
        }

        // Name was not found, error:
        Err(TcError::UnresolvedVariable { name, value: term })
    }
}
