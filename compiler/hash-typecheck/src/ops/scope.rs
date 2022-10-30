//! Functionality related to resolving variables in scopes.

use hash_reporting::diagnostic::Diagnostics;
use hash_source::identifier::Identifier;
use hash_types::{
    arguments::ArgsIdOld,
    location::LocationTarget,
    params::ParamsId,
    scope::{BoundVar, Member, Mutability, ScopeId, ScopeKind, ScopeMember, ScopeVar},
    terms::TermId,
};
use hash_utils::store::Store;
use itertools::Itertools;

use super::{params::pair_args_with_params, AccessToOps};
use crate::{
    diagnostics::{
        error::{TcError, TcResult},
        macros::{tc_panic, tc_panic_on_many},
    },
    storage::{AccessToStorage, StorageRef},
};

/// Contains actions related to variable resolution.
pub struct ScopeManager<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for ScopeManager<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> ScopeManager<'tc> {
    /// Create a new [ScopeManager].
    pub fn new(storage: StorageRef<'tc>) -> Self {
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
            match self.scope_store().map_fast(scope_id, |scope| scope.get(name)) {
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
    pub(crate) fn get_scope_var_member(&self, scope_var: ScopeVar) -> ScopeMember {
        let member = self
            .scope_store()
            .map_fast(scope_var.scope, |scope| scope.get_by_index(scope_var.index));
        ScopeMember { member, scope_id: scope_var.scope, index: scope_var.index }
    }

    /// Get a [ScopeMember] from a [BoundVar].
    ///
    /// The returned member is derived from the parameter list that the variable
    /// is bound to. Furthermore, the originating scope must be either
    /// [ScopeKind::Bound] or [ScopeKind::SetBound]. Otherwise it panics.
    pub(crate) fn get_bound_var_member(
        &self,
        bound_var: BoundVar,
        originating_term: TermId,
    ) -> ScopeMember {
        match self.resolve_name_in_scopes(bound_var.name, originating_term) {
            Ok(scope_member) => {
                let _reader = self.reader();
                self.scope_store().map_fast(scope_member.scope_id, |scope| {
                    if scope.kind != ScopeKind::Bound && scope.kind != ScopeKind::SetBound {
                        tc_panic!(
                            originating_term,
                            self,
                            "Cannot get bound variable member from non-bound scope: {:?}",
                            scope.kind
                        )
                    } else {
                        scope_member
                    }
                })
            }
            Err(_) => {
                tc_panic!(
                    originating_term,
                    self,
                    "Bound var {} not found in current context",
                    bound_var.name
                );
            }
        }
    }

    /// Create a parameter scope, which is a scope that contains all the given
    /// parameters.
    ///
    /// This function is meant to be used for runtime functions, and not type
    /// functions. This is because it creates a variable scope, and assigns each
    /// argument to its type wrapped by `Rt(..)`.
    pub(crate) fn make_rt_param_scope(&self, params_id: ParamsId) -> ScopeId {
        let params = self.reader().get_params_owned(params_id).clone();
        let builder = self.builder();
        let param_scope = builder.create_scope(
            ScopeKind::Variable,
            params.positional().iter().filter_map(|param| {
                Some(Member::variable(
                    param.name?,
                    Mutability::Immutable,
                    param.ty,
                    builder.create_rt_term(param.ty),
                ))
            }),
        );
        param_scope
    }

    /// From a given scope, create a new scope that contains only members
    /// passing the test given by `include_member`.
    ///
    /// Retains scope kind.
    ///
    /// *Note*: `include_member` should not modify/create any scopes.
    pub(crate) fn filter_scope(
        &self,
        scope: ScopeId,
        mut include_member: impl FnMut(&Member) -> bool,
    ) -> ScopeId {
        let (kind, members) = self.scope_store().map_fast(scope, |original_scope| {
            (
                original_scope.kind,
                original_scope
                    .members
                    .iter()
                    .filter(|member| include_member(member))
                    .copied()
                    .collect_vec(),
            )
        });
        self.builder().create_scope(kind, members)
    }

    /// Create a set bound scope, which is a scope that contains all the
    /// mappings in the given arguments, originating from the given
    /// parameters.
    ///
    /// This assigns each parameter name to its corresponding argument value.
    pub(crate) fn make_set_bound_scope(
        &self,
        params_id: ParamsId,
        args_id: ArgsIdOld,
        params_subject: TermId,
        args_subject: TermId,
    ) -> ScopeId {
        let args = self.args_store().get_owned_param_list(args_id);
        let params = self.params_store().get_owned_param_list(params_id);
        let paired = pair_args_with_params(
            &params,
            &args,
            params_id,
            args_id,
            |p| self.typer().infer_arg_from_param(p),
            params_subject,
            args_subject,
        )
        .unwrap_or_else(|err| {
            // This panics because this unification should have occurred in simplifying type
            // function call, so it should have error-ed there.
            self.diagnostics().add_error(err);

            tc_panic_on_many!(
                [params_subject, args_subject],
                self,
                "Could not pair arguments with parameters"
            )
        });

        let builder = self.builder();
        let members = paired
            .iter()
            .filter_map(|(param, arg)| Some(Member::set_bound(param.name?, param.ty, arg.value)));

        builder.create_scope(ScopeKind::SetBound, members)
    }

    /// Create a bound scope, which is a scope that contains all the given
    /// parameters.
    ///
    /// This function is meant to be used for type functions, because it creates
    /// a constant scope and does not assign parameters to any values.
    pub(crate) fn make_bound_scope(&self, params_id: ParamsId) -> ScopeId {
        let params = self.reader().get_params_owned(params_id).clone();
        let builder = self.builder();
        let param_scope = builder.create_scope(
            ScopeKind::Bound,
            params
                .positional()
                .iter()
                .filter_map(|param| Some(Member::bound(param.name?, param.ty))),
        );
        param_scope
    }

    /// Enter the given scope, and run the given callback inside it.
    pub fn enter_scope<T>(&self, scope: ScopeId, f: impl FnOnce(&Self) -> T) -> T {
        self.scopes().append(scope);
        let result = f(self);
        self.scopes().pop_the_scope(scope);
        result
    }

    /// Enter the given scope, and run the given callback inside it, with the
    /// given struct to access storage.
    pub fn enter_scope_with<C: AccessToStorage, T>(
        ctx: &mut C,
        scope: ScopeId,
        f: impl FnOnce(&mut C) -> T,
    ) -> T {
        ctx.scopes().append(scope);
        let result = f(ctx);
        ctx.scopes().pop_the_scope(scope);
        result
    }

    /// Assign the given value to the given member as a `(ScopeId, usize)` pair.
    ///
    /// This will unify the value with the index, decrement the
    /// `assignments_until_closed` counter for the member, and will panic if
    /// the counter is zero already.
    pub fn assign_member(
        &self,
        scope_id: ScopeId,
        index: usize,
        value: TermId,
        site: impl Into<LocationTarget>,
    ) -> TcResult<()> {
        let member = self.scope_store().map_fast(scope_id, |scope| scope.get_by_index(index));

        // Unify types:
        let rhs_ty = self.typer().infer_ty_of_term(value)?;

        let mut err = None;

        if let Err(tc_err) = self.unifier().unify_terms(rhs_ty, member.ty()) {
            err = Some(tc_err);
        }

        self.scope_store().modify_fast(scope_id, |scope| {
            let member = scope.get_mut_by_index(index);
            let member_name = member.name();

            let mut append_err = |tc_err| {
                if err.is_some() {
                    self.diagnostics().add_error(tc_err);
                } else {
                    err = Some(tc_err);
                }
            };

            // @@Todo: add back once this is property implemented
            // if member.is_closed() {
            //     tc_panic!(value, self, "Cannot assign to closed member");
            // }
            match member {
                Member::Bound(_) | Member::SetBound(_) => {
                    // @@Todo: refine this error
                    append_err(TcError::InvalidAssignSubject { location: (scope_id, index).into() })
                }
                Member::Variable(variable) => {
                    // Check that the member is declared as being mutable...
                    if matches!(variable.mutability, Mutability::Immutable) {
                        append_err(TcError::MemberIsImmutable {
                            name: member_name,
                            site: site.into(),
                            decl: (scope_id, index),
                        });
                    } else {
                        // Assign
                        variable.value = value;
                    }
                }
                Member::Constant(constant) => {
                    // @@Todo implement this properly
                    constant.set_value(value);
                }
            };

            err.map_or(Ok(()), Err)
        })
    }

    /// Get the [ScopeKind] of the current scope.
    pub fn current_scope_kind(&self) -> ScopeKind {
        let id = self.scopes().current_scope();
        self.scope_store().map_fast(id, |scope| scope.kind)
    }
}
