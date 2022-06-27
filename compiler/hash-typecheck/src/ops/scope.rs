//! Functionality related to resolving variables in scopes.
use super::AccessToOps;
use crate::{
    error::{TcError, TcResult},
    storage::{primitives::Member, AccessToStorage, StorageRef},
};
use hash_source::identifier::Identifier;

/// Contains actions related to variable resolution.
pub struct ScopeResolver<'gs, 'ls, 'cd> {
    storage: StorageRef<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for ScopeResolver<'gs, 'ls, 'cd> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> ScopeResolver<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRef<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    pub(crate) fn resolve_name_in_scopes(&self, name: Identifier) -> TcResult<Member> {
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
        Err(TcError::UnresolvedVariable { name })
    }
}
