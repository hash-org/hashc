//! Functionality related to resolving variables in scopes.

use super::{AccessToOps, AccessToOpsMut};
use crate::{
    diagnostics::error::{TcError, TcResult},
    storage::{
        primitives::{ParamsId, ScopeId, ScopeMember, Sub, SubSubject, TermId, Visibility},
        AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
    },
};
use hash_source::identifier::Identifier;

/// Contains actions related to variable resolution.
pub struct ScopeResolver<'gs, 'ls, 'cd, 's> {
    /// Inner storage for global, local and core definitions.
    storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for ScopeResolver<'gs, 'ls, 'cd, 's> {
    /// Get the inner storage for resolving.
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}
impl<'gs, 'ls, 'cd, 's> AccessToStorageMut for ScopeResolver<'gs, 'ls, 'cd, 's> {
    /// Get the inner storage for resolving.
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 's> ScopeResolver<'gs, 'ls, 'cd, 's> {
    /// Create a new [ScopeResolver].
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd, 's>) -> Self {
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
    ) -> TcResult<ScopeMember> {
        // Here, we have to look in the scopes:
        for scope_id in self.scopes().iter_up() {
            match self.reader().get_scope(scope_id).get(name) {
                // Found in this scope, return the member.
                Some((member, index)) => return Ok(ScopeMember { member, scope_id, index }),
                // Continue to the next (higher) scope:
                None => continue,
            }
        }

        // Name was not found, error:
        Err(TcError::UnresolvedVariable { name, value: term })
    }

    /// Enter a parameter scope, which is a scope that contains all the given
    /// parameters.
    ///
    /// This function is meant to be used for runtime functions, and not type
    /// functions. This is because it creates a variable scope, and assigns each
    /// argument to its type wrapped by `Rt(..)`.
    pub(crate) fn enter_rt_param_scope(&mut self, params_id: ParamsId) -> ScopeId {
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

    /// Enter a substitution, which is a scope that contains all the mappings in
    /// the given substitution.
    ///
    /// This is creates a constant scope, and assigns each domain element of
    /// type [SubSubject::Var] to its corresponding range element.
    pub(crate) fn enter_sub_param_scope(&mut self, sub: &Sub) -> ScopeId {
        let builder = self.builder();
        let sub_scope =
            builder.create_constant_scope(sub.pairs().filter_map(|(domain_el, range_el)| {
                match domain_el {
                    SubSubject::Var(var) => Some(builder.create_constant_member_infer_ty(
                        var.name,
                        range_el,
                        Visibility::Private,
                    )),
                    SubSubject::Unresolved(_) => None,
                }
            }));
        self.scopes_mut().append(sub_scope);
        sub_scope
    }

    /// Enter a parameter scope, which is a scope that contains all the given
    /// parameters.
    ///
    /// This function is meant to be used for type functions, because it creates
    /// a constant scope and does not assign parameters to any values.
    pub(crate) fn enter_ty_param_scope(&mut self, params_id: ParamsId) -> ScopeId {
        let params = self.reader().get_params(params_id).clone();
        let builder = self.builder();
        let param_scope =
            builder.create_constant_scope(params.positional().iter().filter_map(|param| {
                Some(builder.create_uninitialised_constant_member(
                    param.name?,
                    param.ty,
                    Visibility::Private,
                ))
            }));
        self.scopes_mut().append(param_scope);
        param_scope
    }
}
