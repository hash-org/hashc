//! Functionality related to resolving variables in scopes.

// @@Temporary
#![allow(dead_code)]

use super::{AccessToOps, AccessToOpsMut};
use crate::{
    diagnostics::error::{TcError, TcResult},
    storage::{
        primitives::{Member, ParamsId, ScopeId, TermId},
        AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
    },
};
use hash_source::identifier::Identifier;

/// Contains actions related to variable resolution.
pub struct ScopeResolver<'gs, 'ls, 'cd> {
    /// Inner storage for global, local and core definitions.
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for ScopeResolver<'gs, 'ls, 'cd> {
    /// Get the inner storage for resolving.
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}
impl<'gs, 'ls, 'cd> AccessToStorageMut for ScopeResolver<'gs, 'ls, 'cd> {
    /// Get the inner storage for resolving.
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd> ScopeResolver<'gs, 'ls, 'cd> {
    /// Create a new [ScopeResolver].
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
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

    pub(crate) fn enter_param_scope(&mut self, params_id: ParamsId) -> ScopeId {
        let params = self.reader().get_params(params_id).clone();
        let builder = self.builder();
        let param_scope =
            builder.create_variable_scope(params.positional().iter().filter_map(|param| {
                Some(builder.create_variable_member(
                    param.name?,
                    param.ty,
                    builder.create_rt_term(param.ty),
                ))
            }));
        self.scopes_mut().append(param_scope);
        param_scope
    }
}
