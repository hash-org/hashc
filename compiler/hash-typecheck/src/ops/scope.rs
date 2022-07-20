//! Functionality related to resolving variables in scopes.

use super::{params::pair_args_with_params, AccessToOps, AccessToOpsMut};
use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::tc_panic_on_many,
        reporting::TcErrorWithStorage,
    },
    storage::{
        primitives::{
            ArgsId, Member, MemberData, Mutability, ParamsId, ScopeId, ScopeKind, ScopeMember,
            ScopeVar, TermId, Visibility,
        },
        AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
    },
};
use hash_reporting::{report::Report, writer};
use hash_source::identifier::Identifier;

/// Contains actions related to variable resolution.
pub struct ScopeManager<'gs, 'ls, 'cd, 's> {
    storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for ScopeManager<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}
impl<'gs, 'ls, 'cd, 's> AccessToStorageMut for ScopeManager<'gs, 'ls, 'cd, 's> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 's> ScopeManager<'gs, 'ls, 'cd, 's> {
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

    /// Get a [ScopeMember] from a [ScopeVar].
    pub(crate) fn get_scope_member_from_var(&mut self, scope_var: ScopeVar) -> ScopeMember {
        let reader = self.reader();
        let member = reader.get_scope(scope_var.scope_id).get_by_index(scope_var.index);
        ScopeMember { member, scope_id: scope_var.scope_id, index: scope_var.index }
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
        let param_scope = builder.create_scope(
            ScopeKind::Variable,
            params.positional().iter().filter_map(|param| {
                Some(builder.create_variable_member(
                    param.name?,
                    param.ty,
                    builder.create_rt_term(param.ty),
                ))
            }),
        );
        self.scopes_mut().append(param_scope);
        param_scope
    }

    /// Enter a set bound scope, which is a scope that contains all the mappings
    /// in the given arguments, originating from the given parameters.
    ///
    /// This assigns each parameter name to its corresponding argument value.
    pub(crate) fn _enter_set_bound_scope(
        &mut self,
        params_id: ParamsId,
        args_id: ArgsId,
        params_subject: TermId,
        args_subject: TermId,
    ) -> ScopeId {
        let args = self.args_store().get(args_id).clone();
        let params = self.params_store().get(params_id).clone();
        let paired =
            pair_args_with_params(&params, &args, params_id, args_id, params_subject, args_subject)
                .unwrap_or_else(|err| {
                    let report: Report = TcErrorWithStorage::new(err, self.storages()).into();
                    eprintln!("{}", writer::ReportWriter::new(report, self.source_map()));
                    tc_panic_on_many!(
                        [params_subject, args_subject],
                        self,
                        "Could not pair arguments with parameters"
                    )
                });

        let builder = self.builder();
        let members = paired.iter().filter_map(|(param, arg)| {
            Some(Member::closed(
                param.name?,
                Visibility::Private,
                Mutability::Immutable,
                MemberData::from_ty_and_value(None, Some(arg.value)),
            ))
        });
        let sub_scope = builder.create_scope(ScopeKind::SetBound, members);
        self.scopes_mut().append(sub_scope);
        sub_scope
    }

    /// Enter a bound scope, which is a scope that contains all the given
    /// parameters.
    ///
    /// This function is meant to be used for type functions, because it creates
    /// a constant scope and does not assign parameters to any values.
    pub(crate) fn enter_bound_scope(&mut self, params_id: ParamsId) -> ScopeId {
        let params = self.reader().get_params(params_id).clone();
        let builder = self.builder();
        let param_scope = builder.create_scope(
            ScopeKind::Bound,
            params.positional().iter().filter_map(|param| {
                Some(builder.create_uninitialised_constant_member(
                    param.name?,
                    param.ty,
                    Visibility::Private,
                ))
            }),
        );
        self.scopes_mut().append(param_scope);
        param_scope
    }

    /// Assign the given value to the given member as a `(ScopeId, usize)` pair.
    ///
    /// This will unify the value with the index, decrement the
    /// `assignments_until_closed` counter for the member, and will panic if
    /// the counter is zero already.
    pub fn assign_member(
        &mut self,
        scope_id: ScopeId,
        index: usize,
        value: TermId,
    ) -> TcResult<()> {
        let member = self.scope_store_mut().get_mut(scope_id).get_by_index(index);

        // Unify types:
        let member_data = self.typer().infer_member_ty(member.data)?;
        let rhs_ty = self.typer().infer_ty_of_term(value)?;
        let _ = self.unifier().unify_terms(rhs_ty, member_data.ty)?;

        let member = self.scope_store_mut().get_mut(scope_id).get_mut_by_index(index);
        // @@Todo: add back once this is property implemented
        // if member.is_closed() {
        //     tc_panic!(value, self, "Cannot assign to closed member");
        // }

        member.assignments_until_closed -= 1;
        match member.data {
            MemberData::Uninitialised { .. } => {
                member.data = MemberData::InitialisedWithInferredTy { value }
            }
            MemberData::InitialisedWithTy { ty, .. } => {
                member.data = MemberData::InitialisedWithTy { value, ty }
            }
            MemberData::InitialisedWithInferredTy { .. } => {
                member.data = MemberData::InitialisedWithInferredTy { value }
            }
        }

        Ok(())
    }
}
