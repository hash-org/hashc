//! Functionality related to discovering variables in terms.
use std::collections::HashSet;

use hash_utils::store::{SequenceStore, SequenceStoreKey, Store};

use super::AccessToOps;
use crate::{
    diagnostics::{error::TcResult, macros::tc_panic},
    storage::{
        arguments::ArgsId,
        params::ParamsId,
        primitives::{
            AccessTerm, Arg, BoundVar, Level0Term, Level1Term, Level2Term, Level3Term, Member,
            NominalDef, Param, StructDef, StructFields, Sub, SubVar, Term, TyFn, TyFnCase,
        },
        scope::ScopeId,
        terms::TermId,
        AccessToStorage, StorageRef,
    },
};

/// Contains actions related to variable discovery.
pub struct Discoverer<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for Discoverer<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> Discoverer<'tc> {
    pub(crate) fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Add the free variables in the parameter default values and types to the
    /// given [HashSet].
    pub(crate) fn add_free_sub_vars_in_params_to_set(
        &self,
        params_id: ParamsId,
        result: &mut HashSet<SubVar>,
    ) {
        self.params_store().map_as_param_list_fast(params_id, |params| {
            // Add default value and type free vars
            for param in params.positional() {
                self.add_free_sub_vars_in_term_to_set(param.ty, result);
                if let Some(default_value_id) = param.default_value {
                    self.add_free_sub_vars_in_term_to_set(default_value_id, result);
                }
            }
        })
    }

    /// Add the free variables that exist in the given args, to the given
    /// [HashSet].
    pub(crate) fn add_free_sub_vars_in_args_to_set(
        &self,
        args_id: ArgsId,
        result: &mut HashSet<SubVar>,
    ) {
        self.args_store().map_as_param_list_fast(args_id, |args| {
            for arg in args.positional() {
                self.add_free_sub_vars_in_term_to_set(arg.value, result);
            }
        })
    }

    /// Add the free variables that exist in the given [Level0Term], to the
    /// given [HashSet].
    pub(crate) fn add_free_sub_vars_in_level0_term_to_set(
        &self,
        term: &Level0Term,
        result: &mut HashSet<SubVar>,
    ) {
        match term {
            Level0Term::Rt(ty_term_id) => {
                self.add_free_sub_vars_in_term_to_set(*ty_term_id, result)
            }
            Level0Term::FnLit(fn_lit) => {
                // Forward to fn type and return value
                self.add_free_sub_vars_in_term_to_set(fn_lit.fn_ty, result);
                self.add_free_sub_vars_in_term_to_set(fn_lit.return_value, result);
            }
            Level0Term::FnCall(fn_call) => {
                // Forward to subject and args:
                self.add_free_sub_vars_in_term_to_set(fn_call.subject, result);
                self.add_free_sub_vars_in_args_to_set(fn_call.args, result);
            }
            Level0Term::Tuple(tuple_lit) => {
                self.add_free_sub_vars_in_args_to_set(tuple_lit.members, result);
            }
            Level0Term::Constructed(constructed) => {
                self.add_free_sub_vars_in_term_to_set(constructed.subject, result);
                self.add_free_sub_vars_in_args_to_set(constructed.members, result);
            }
            Level0Term::EnumVariant(_) | Level0Term::Lit(_) | Level0Term::Unit(_) => {}
        }
    }

    /// Add the free variables that exist in the given [Level1Term], to the
    /// given [HashSet].
    pub(crate) fn add_free_sub_vars_in_level1_term_to_set(
        &self,
        term: &Level1Term,
        result: &mut HashSet<SubVar>,
    ) {
        match term {
            Level1Term::ModDef(_) | Level1Term::NominalDef(_) => {}
            Level1Term::Tuple(tuple_ty) => {
                // Add the free variables in the parameters (don't remove the parameter names)
                self.add_free_sub_vars_in_params_to_set(tuple_ty.members, result);
            }
            Level1Term::Fn(fn_ty) => {
                // Add the free variables in the parameters and return type.
                self.add_free_sub_vars_in_params_to_set(fn_ty.params, result);
                self.add_free_sub_vars_in_term_to_set(fn_ty.return_ty, result);
            }
        }
    }

    /// Add the free variables that exist in the given term, to the given
    /// [HashSet].
    ///
    /// Free variables are either `Var` or `Unresolved`, and this function
    /// collects both.
    pub(crate) fn add_free_sub_vars_in_term_to_set(
        &self,
        term_id: TermId,
        result: &mut HashSet<SubVar>,
    ) {
        let reader = self.reader();
        let term = reader.get_term(term_id);
        match term {
            Term::Unresolved(unresolved) => {
                // Found a free variable:
                result.insert(unresolved.into());
            }
            Term::Access(term) => {
                // Free vars in the subject:
                self.add_free_sub_vars_in_term_to_set(term.subject, result);
            }
            Term::Merge(terms) => {
                // Free vars in each term:
                for idx in terms.to_index_range() {
                    let inner_term_id = self.term_list_store().get_at_index(terms, idx);
                    self.add_free_sub_vars_in_term_to_set(inner_term_id, result);
                }
            }
            Term::Union(terms) => {
                // Free vars in each term:
                for idx in terms.to_index_range() {
                    let inner_term_id = self.term_list_store().get_at_index(terms, idx);
                    self.add_free_sub_vars_in_term_to_set(inner_term_id, result);
                }
            }
            Term::TyFn(ty_fn) => {
                // Free vars in params, return
                self.add_free_sub_vars_in_params_to_set(ty_fn.general_params, result);
                self.add_free_sub_vars_in_term_to_set(ty_fn.general_return_ty, result);
                for case in &ty_fn.cases {
                    self.add_free_sub_vars_in_params_to_set(case.params, result);
                    self.add_free_sub_vars_in_term_to_set(case.return_ty, result);
                    self.add_free_sub_vars_in_term_to_set(case.return_value, result);
                }
            }
            Term::TyFnTy(ty_fn_ty) => {
                // Free vars in params, return
                self.add_free_sub_vars_in_params_to_set(ty_fn_ty.params, result);
                self.add_free_sub_vars_in_term_to_set(ty_fn_ty.return_ty, result);
            }
            Term::TyFnCall(app_ty_fn) => {
                // Free vars in subject and args
                self.add_free_sub_vars_in_term_to_set(app_ty_fn.subject, result);
                self.add_free_sub_vars_in_args_to_set(app_ty_fn.args, result);
            }
            Term::SetBound(set_bound) => {
                // Free vars in inner term
                // @@PotentiallyIncomplete: do we need to look at the set bound scope here?
                self.add_free_sub_vars_in_term_to_set(set_bound.term, result);
            }
            Term::TyOf(term) => {
                self.add_free_sub_vars_in_term_to_set(term, result);
            }
            // Definite-level terms:
            Term::Level3(_) | Term::Level2(_) => {}
            Term::Level1(term) => {
                self.add_free_sub_vars_in_level1_term_to_set(&term, result);
            }
            Term::Level0(term) => {
                self.add_free_sub_vars_in_level0_term_to_set(&term, result);
            }
            // No vars:
            Term::Var(_) | Term::Root | Term::ScopeVar(_) | Term::BoundVar(_) => {}
        }
    }

    /// Add the free variables that exist in the given [Sub], to the
    /// given [HashSet] (minus the ones that will be substituted)..
    pub(crate) fn add_free_sub_vars_in_sub_to_set(&self, sub: &Sub, result: &mut HashSet<SubVar>) {
        let mut intermediate_result = HashSet::new();

        // Add all the variables in the range, minus the variables in the domain:
        for r in sub.range() {
            self.add_free_sub_vars_in_term_to_set(r, &mut intermediate_result);
        }
        let mut domain_vars = HashSet::new();
        for d in sub.range() {
            self.add_free_sub_vars_in_term_to_set(d, &mut domain_vars);
        }
        // Remove all the variables in domain_vars:
        for d in domain_vars {
            intermediate_result.remove(&d);
        }

        result.extend(intermediate_result);
    }

    /// Get the free variables that exist in the given [Sub] (minus the ones
    /// that will be substituted).
    pub(crate) fn get_free_sub_vars_in_sub(&self, sub: &Sub) -> HashSet<SubVar> {
        let mut result = HashSet::new();
        self.add_free_sub_vars_in_sub_to_set(sub, &mut result);
        result
    }

    /// Get the set of free variables that exist in the given term.
    ///
    /// Free variables are either `Var` or `Unresolved`, and this function
    /// collects both.
    pub(crate) fn get_free_sub_vars_in_term(&self, term_id: TermId) -> HashSet<SubVar> {
        let mut result = HashSet::new();
        self.add_free_sub_vars_in_term_to_set(term_id, &mut result);
        result
    }

    /// Add the free variables in the parameter default values and types to the
    /// given [HashSet].
    pub(crate) fn add_free_bound_vars_in_params_to_set(
        &self,
        params_id: ParamsId,
        result: &mut HashSet<BoundVar>,
    ) {
        self.params_store().map_as_param_list_fast(params_id, |params| {
            // Add default value and type free vars
            for param in params.positional() {
                self.add_free_bound_vars_in_term_to_set(param.ty, result);
                if let Some(default_value_id) = param.default_value {
                    self.add_free_bound_vars_in_term_to_set(default_value_id, result);
                }
            }
        })
    }

    /// Add the parameter variables in the parameters to the given [HashSet] as
    /// [BoundVar]s.
    pub(crate) fn add_param_vars_as_bound_vars_to_set(
        &self,
        params_id: ParamsId,
        result: &mut HashSet<BoundVar>,
    ) {
        self.params_store().map_as_param_list_fast(params_id, |params| {
            // Add default value and type free vars
            for param in params.positional() {
                if let Some(name) = param.name {
                    result.insert(BoundVar { name });
                }
            }
        })
    }

    /// Add the free variables that exist in the given args, to the given
    /// [HashSet].
    pub(crate) fn add_free_bound_vars_in_args_to_set(
        &self,
        args_id: ArgsId,
        result: &mut HashSet<BoundVar>,
    ) {
        self.args_store().map_as_param_list_fast(args_id, |args| {
            for arg in args.positional() {
                self.add_free_bound_vars_in_term_to_set(arg.value, result);
            }
        })
    }

    /// Add the free variables that exist in the given [Level0Term], to the
    /// given [HashSet].
    pub(crate) fn add_free_bound_vars_in_level0_term_to_set(
        &self,
        term: &Level0Term,
        result: &mut HashSet<BoundVar>,
    ) {
        match term {
            Level0Term::Rt(ty_term_id) => {
                self.add_free_bound_vars_in_term_to_set(*ty_term_id, result)
            }
            Level0Term::FnLit(fn_lit) => {
                // Forward to fn type and return value
                self.add_free_bound_vars_in_term_to_set(fn_lit.fn_ty, result);
                self.add_free_bound_vars_in_term_to_set(fn_lit.return_value, result);
            }
            Level0Term::FnCall(fn_call) => {
                // Forward to subject and args:
                self.add_free_bound_vars_in_term_to_set(fn_call.subject, result);
                self.add_free_bound_vars_in_args_to_set(fn_call.args, result);
            }
            Level0Term::Tuple(tuple_lit) => {
                self.add_free_bound_vars_in_args_to_set(tuple_lit.members, result);
            }
            Level0Term::Constructed(constructed) => {
                self.add_free_bound_vars_in_term_to_set(constructed.subject, result);
                self.add_free_bound_vars_in_args_to_set(constructed.members, result);
            }
            Level0Term::EnumVariant(_) | Level0Term::Lit(_) | Level0Term::Unit(_) => {}
        }
    }

    /// Add the free variables that exist in the given [Level2Term], to the
    /// given [HashSet].
    pub(crate) fn add_free_bound_vars_in_level2_term_to_set(
        &self,
        term: &Level2Term,
        result: &mut HashSet<BoundVar>,
    ) {
        match term {
            Level2Term::Trt(trt_def_id) => {
                // Look at the scope of the trait def
                let trt_def_scope = self.reader().get_trt_def(*trt_def_id).members;
                self.add_free_bound_vars_in_scope_to_set(trt_def_scope, result)
            }
            Level2Term::AnyTy | Level2Term::SizedTy => {}
        }
    }

    /// Add the free variables that exist in the given [Level1Term], to the
    /// given [HashSet].
    pub(crate) fn add_free_bound_vars_in_level1_term_to_set(
        &self,
        term: &Level1Term,
        result: &mut HashSet<BoundVar>,
    ) {
        match term {
            Level1Term::ModDef(mod_def_id) => {
                // Look at the scope of the mod def
                let mod_def_scope = self.reader().get_mod_def(*mod_def_id).members;
                self.add_free_bound_vars_in_scope_to_set(mod_def_scope, result)
            }
            Level1Term::NominalDef(nominal_def_id) => {
                // Look at the scope of the nominal def
                let reader = self.reader();
                let nominal_def = reader.get_nominal_def(*nominal_def_id);
                match nominal_def {
                    NominalDef::Struct(StructDef {
                        fields: StructFields::Explicit(fields),
                        ..
                    }) => self.add_free_bound_vars_in_params_to_set(fields, result),
                    // @@Todo: add bound vars to opaque structs
                    NominalDef::Struct(_) | NominalDef::Unit(_) => {}
                    // @@Remove: enums will be removed anyway.
                    NominalDef::Enum(_) => {}
                }
            }
            Level1Term::Tuple(tuple_ty) => {
                // Add the free variables in the parameters (don't remove the parameter names)
                self.add_free_bound_vars_in_params_to_set(tuple_ty.members, result);
            }
            Level1Term::Fn(fn_ty) => {
                // Add the free variables in the parameters and return type.
                self.add_free_bound_vars_in_params_to_set(fn_ty.params, result);
                self.add_free_bound_vars_in_term_to_set(fn_ty.return_ty, result);
            }
        }
    }

    /// Add the free variables that exist in the given [ScopeId], to the
    /// given [HashSet].
    ///
    /// This adds the free (bound) variables in the member types and values.
    pub(crate) fn add_free_bound_vars_in_scope_to_set(
        &self,
        scope: ScopeId,
        result: &mut HashSet<BoundVar>,
    ) {
        let reader = self.reader();
        let scope = reader.get_scope_copy(scope);
        for member in scope.iter() {
            self.add_free_bound_vars_in_term_to_set(member.ty(), result);
            if let Some(value) = member.value() {
                self.add_free_bound_vars_in_term_to_set(value, result)
            }
        }
    }

    /// Add the free variables that exist in the given term, to the given
    /// [HashSet].
    ///
    /// Free variables are either `Var` or `Unresolved`, and this function
    /// collects both.
    pub(crate) fn add_free_bound_vars_in_term_to_set(
        &self,
        term_id: TermId,
        result: &mut HashSet<BoundVar>,
    ) {
        let reader = self.reader();
        let term = reader.get_term(term_id);
        match term {
            Term::BoundVar(var) => {
                // Found a bound var
                result.insert(var);
            }
            Term::Access(term) => {
                // Free vars in the subject:
                self.add_free_bound_vars_in_term_to_set(term.subject, result);
            }
            Term::Merge(terms) => {
                // Free vars in each term:
                for idx in terms.to_index_range() {
                    let inner_term_id = self.term_list_store().get_at_index(terms, idx);
                    self.add_free_bound_vars_in_term_to_set(inner_term_id, result);
                }
            }
            Term::Union(terms) => {
                // Free vars in each term:
                for idx in terms.to_index_range() {
                    let inner_term_id = self.term_list_store().get_at_index(terms, idx);
                    self.add_free_bound_vars_in_term_to_set(inner_term_id, result);
                }
            }
            Term::TyFn(ty_fn) => {
                // Keep track of the variables here cause we have to subtract the ones in the
                // params before adding them to result.
                let mut ty_fn_params_result = HashSet::new();
                let mut ty_fn_bound_vars_due_to_params = HashSet::new();
                let mut ty_fn_result = HashSet::new();

                self.add_free_bound_vars_in_params_to_set(
                    ty_fn.general_params,
                    &mut ty_fn_params_result,
                );
                self.add_param_vars_as_bound_vars_to_set(
                    ty_fn.general_params,
                    &mut ty_fn_bound_vars_due_to_params,
                );
                self.add_free_bound_vars_in_term_to_set(ty_fn.general_return_ty, &mut ty_fn_result);
                for case in &ty_fn.cases {
                    self.add_free_bound_vars_in_params_to_set(
                        case.params,
                        &mut ty_fn_params_result,
                    );
                    self.add_param_vars_as_bound_vars_to_set(
                        case.params,
                        &mut ty_fn_bound_vars_due_to_params,
                    );
                    self.add_free_bound_vars_in_term_to_set(case.return_ty, &mut ty_fn_result);
                    self.add_free_bound_vars_in_term_to_set(case.return_value, &mut ty_fn_result);
                }

                // Subtract the bound vars in the params from the result, and add the bound vars
                // in the types and default values of the params.
                result.extend(
                    ty_fn_result
                        .difference(&ty_fn_bound_vars_due_to_params)
                        .chain(&ty_fn_params_result),
                );
            }
            Term::TyFnTy(ty_fn_ty) => {
                // Same basic procedure as for TyFn.
                let mut ty_fn_params_result = HashSet::new();
                let mut ty_fn_bound_vars_due_to_params = HashSet::new();
                let mut ty_fn_result = HashSet::new();

                self.add_free_bound_vars_in_params_to_set(
                    ty_fn_ty.params,
                    &mut ty_fn_params_result,
                );
                self.add_param_vars_as_bound_vars_to_set(
                    ty_fn_ty.params,
                    &mut ty_fn_bound_vars_due_to_params,
                );
                self.add_free_bound_vars_in_term_to_set(ty_fn_ty.return_ty, &mut ty_fn_result);

                result.extend(
                    ty_fn_result
                        .difference(&ty_fn_bound_vars_due_to_params)
                        .chain(&ty_fn_params_result),
                );
            }
            Term::TyFnCall(app_ty_fn) => {
                // Free vars in subject and args
                self.add_free_bound_vars_in_term_to_set(app_ty_fn.subject, result);
                self.add_free_bound_vars_in_args_to_set(app_ty_fn.args, result);
            }
            Term::SetBound(set_bound) => {
                // Free vars in inner term and in the bound scope.
                self.add_free_bound_vars_in_scope_to_set(set_bound.scope, result);
                self.add_free_bound_vars_in_term_to_set(set_bound.term, result);
            }
            Term::TyOf(term) => {
                self.add_free_bound_vars_in_term_to_set(term, result);
            }
            Term::Level2(term) => {
                self.add_free_bound_vars_in_level2_term_to_set(&term, result);
            }
            Term::Level1(term) => {
                self.add_free_bound_vars_in_level1_term_to_set(&term, result);
            }
            Term::Level0(term) => {
                self.add_free_bound_vars_in_level0_term_to_set(&term, result);
            }
            // No bound vars:
            Term::Var(_)
            | Term::Root
            | Term::ScopeVar(_)
            | Term::Unresolved(_)
            | Term::Level3(_) => {}
        }
    }

    /// Get the set of free variables that exist in the given term.
    ///
    /// Free variables are either `Var` or `Unresolved`, and this function
    /// collects both.
    pub fn get_free_bound_vars_in_term(&self, term_id: TermId) -> HashSet<BoundVar> {
        let mut result = HashSet::new();
        self.add_free_bound_vars_in_term_to_set(term_id, &mut result);
        result
    }

    pub(crate) fn apply_set_bound_to_params_with_flag(
        &self,
        set_bound_scope_id: ScopeId,
        params_id: ParamsId,
        ignore_bound_vars: &HashSet<BoundVar>,
        applied_once: &mut bool,
    ) -> TcResult<ParamsId> {
        let result = self.params_store().map_as_param_list(params_id, |params| {
            params
                .positional()
                .iter()
                .map(|param| {
                    Ok(Param {
                        name: param.name,
                        ty: self.apply_set_bound_to_term_with_flag(
                            set_bound_scope_id,
                            param.ty,
                            ignore_bound_vars,
                            applied_once,
                        )?,
                        default_value: param
                            .default_value
                            .map(|value| {
                                self.apply_set_bound_to_term_with_flag(
                                    set_bound_scope_id,
                                    value,
                                    ignore_bound_vars,
                                    applied_once,
                                )
                            })
                            .transpose()?,
                    })
                })
                .collect::<TcResult<Vec<_>>>()
        })?;
        let params_origin = self.params_store().get_origin(params_id);

        let new_params = self.builder().create_params(result, params_origin);
        self.location_store().copy_locations(params_id, new_params);

        Ok(new_params)
    }

    /// Apply the given [Scope] of kind [Scope::SetBound] to the given params,
    /// at the lowest level possible.
    pub(crate) fn apply_set_bound_to_params(
        &self,
        set_bound_scope_id: ScopeId,
        params_id: ParamsId,
    ) -> TcResult<ParamsId> {
        self.apply_set_bound_to_params_with_flag(
            set_bound_scope_id,
            params_id,
            &HashSet::new(),
            &mut false,
        )
    }

    pub(crate) fn apply_set_bound_to_args_with_flag(
        &self,
        set_bound_scope_id: ScopeId,
        args_id: ArgsId,
        ignore_bound_vars: &HashSet<BoundVar>,
        applied_once: &mut bool,
    ) -> TcResult<ArgsId> {
        let result = self.args_store().map_as_param_list(args_id, |args| {
            args.positional()
                .iter()
                .map(|arg| {
                    Ok(Arg {
                        name: arg.name,
                        value: self.apply_set_bound_to_term_with_flag(
                            set_bound_scope_id,
                            arg.value,
                            ignore_bound_vars,
                            applied_once,
                        )?,
                    })
                })
                .collect::<TcResult<Vec<_>>>()
        })?;
        let args_origin = self.args_store().get_origin(args_id);

        let new_args = self.builder().create_args(result, args_origin);
        self.location_store().copy_locations(args_id, new_args);
        Ok(new_args)
    }

    /// Apply the given [Scope] of kind [Scope::SetBound] to the given args, at
    /// the lowest level possible.
    pub(crate) fn apply_set_bound_to_args(
        &self,
        set_bound_scope_id: ScopeId,
        args_id: ArgsId,
    ) -> TcResult<ArgsId> {
        self.apply_set_bound_to_args_with_flag(
            set_bound_scope_id,
            args_id,
            &HashSet::new(),
            &mut false,
        )
    }

    /// Apply the given [Scope] of kind [Scope::SetBound] to the given term, at
    /// the lowest level possible.
    pub(crate) fn potentially_apply_set_bound_to_term(
        &self,
        set_bound_scope_id: ScopeId,
        term_id: TermId,
    ) -> TcResult<TermId> {
        Ok(self
            .apply_set_bound_to_term_rec(set_bound_scope_id, term_id, &HashSet::new())?
            .unwrap_or(term_id))
    }

    /// Apply the given [Scope] of kind [Scope::SetBound] to the given term, at
    /// the lowest level possible. Returns None if no application occurred.
    pub(crate) fn apply_set_bound_to_term(
        &self,
        set_bound_scope_id: ScopeId,
        term_id: TermId,
    ) -> TcResult<Option<TermId>> {
        self.apply_set_bound_to_term_rec(set_bound_scope_id, term_id, &HashSet::new())
    }

    // Same as [Self::apply_set_bound_to_term] but if it returns None, the original
    // term is returned, with a flag to indicate if the term is the original or
    // the modified.
    pub(crate) fn apply_set_bound_to_term_with_flag(
        &self,
        set_bound_scope_id: ScopeId,
        term_id: TermId,
        ignore_bound_vars: &HashSet<BoundVar>,
        applied_once: &mut bool,
    ) -> TcResult<TermId> {
        Ok(self
            .apply_set_bound_to_term_rec(set_bound_scope_id, term_id, ignore_bound_vars)?
            .map(|applied| {
                *applied_once = true;
                applied
            })
            .unwrap_or(term_id))
    }

    /// Apply the given [Scope] of kind [Scope::SetBound] to the given term, at
    /// the lowest level possible. Returns None if no application occurred.
    ///
    /// This checks each child of the term, and only wraps it in a set bound if
    /// the free variables are present.
    ///
    /// Takes a list of bound vars to ignore, because they are bound in some
    /// child scope (like a type function bound).
    pub(crate) fn apply_set_bound_to_term_rec(
        &self,
        set_bound_scope_id: ScopeId,
        term_id: TermId,
        ignore_bound_vars: &HashSet<BoundVar>,
    ) -> TcResult<Option<TermId>> {
        let reader = self.reader();
        let term = reader.get_term(term_id);
        let result = match term {
            Term::BoundVar(var) => {
                if ignore_bound_vars.contains(&var) {
                    Ok(None)
                } else {
                    // Try to resolve the bound var
                    match self
                        .scope_store()
                        .map_fast(set_bound_scope_id, |scope| scope.get(var.name))
                    {
                        Some((member, _)) => {
                            let value = match member {
                                Member::SetBound(set_bound) => set_bound.value,
                                _ => {
                                    tc_panic!(
                                        term_id,
                                        self,
                                        "Found non set bound member in set bound scope"
                                    )
                                }
                            };
                            // @@Correctness: do we need to recurse here?
                            Ok(Some(self.apply_set_bound_to_term_with_flag(
                                set_bound_scope_id,
                                value,
                                ignore_bound_vars,
                                &mut false,
                            )?))
                        }
                        None => {
                            // Not part of the given scope:
                            Ok(None)
                        }
                    }
                }
            }
            Term::Access(term) => {
                // Apply to subject
                let subject_applied = self.apply_set_bound_to_term_rec(
                    set_bound_scope_id,
                    term.subject,
                    ignore_bound_vars,
                )?;
                match subject_applied {
                    Some(subject_applied) => {
                        Ok(Some(self.builder().create_term(Term::Access(AccessTerm {
                            subject: subject_applied,
                            ..term
                        }))))
                    }
                    None => Ok(None),
                }
            }
            Term::Merge(terms) => {
                // Apply each term:
                let terms = terms;
                let mut applied_once = false;
                let merge_applied = self
                    .reader()
                    .get_term_list_owned(terms)
                    .iter()
                    .map(|term| {
                        self.apply_set_bound_to_term_with_flag(
                            set_bound_scope_id,
                            *term,
                            ignore_bound_vars,
                            &mut applied_once,
                        )
                    })
                    .collect::<TcResult<Vec<_>>>()?;
                if !applied_once {
                    Ok(None)
                } else {
                    Ok(Some(self.builder().create_merge_term(merge_applied)))
                }
            }
            Term::Union(terms) => {
                // Apply each term:
                let terms = terms;
                let mut applied_once = false;
                let union_applied = self
                    .reader()
                    .get_term_list_owned(terms)
                    .iter()
                    .map(|term| {
                        self.apply_set_bound_to_term_with_flag(
                            set_bound_scope_id,
                            *term,
                            ignore_bound_vars,
                            &mut applied_once,
                        )
                    })
                    .collect::<TcResult<Vec<_>>>()?;
                if !applied_once {
                    Ok(None)
                } else {
                    Ok(Some(self.builder().create_union_term(union_applied)))
                }
            }
            Term::TyFn(ty_fn) => {
                // Keep track of the param variables here cause we have to subtract the ones in
                // the params before traversing.
                let ty_fn = ty_fn;
                let mut applied_once = false;
                let mut ty_fn_bound_vars_due_to_params = HashSet::new();
                self.add_param_vars_as_bound_vars_to_set(
                    ty_fn.general_params,
                    &mut ty_fn_bound_vars_due_to_params,
                );
                let new_ignore_bound_vars = ignore_bound_vars
                    .union(&ty_fn_bound_vars_due_to_params)
                    .copied()
                    .collect::<HashSet<_>>();

                let general_params = self.apply_set_bound_to_params_with_flag(
                    set_bound_scope_id,
                    ty_fn.general_params,
                    ignore_bound_vars,
                    &mut applied_once,
                )?;
                let general_return_ty = self.apply_set_bound_to_term_with_flag(
                    set_bound_scope_id,
                    ty_fn.general_return_ty,
                    &new_ignore_bound_vars,
                    &mut applied_once,
                )?;

                let cases = ty_fn
                    .cases
                    .iter()
                    .map(|case| {
                        // Keep track of the param variables for cases too
                        let mut ty_fn_bound_vars_due_to_params = HashSet::new();
                        self.add_param_vars_as_bound_vars_to_set(
                            ty_fn.general_params,
                            &mut ty_fn_bound_vars_due_to_params,
                        );
                        let new_ignore_bound_vars = ignore_bound_vars
                            .union(&ty_fn_bound_vars_due_to_params)
                            .copied()
                            .collect::<HashSet<_>>();
                        let params = self.apply_set_bound_to_params_with_flag(
                            set_bound_scope_id,
                            case.params,
                            ignore_bound_vars,
                            &mut applied_once,
                        )?;
                        let return_ty = self.apply_set_bound_to_term_with_flag(
                            set_bound_scope_id,
                            case.return_ty,
                            &new_ignore_bound_vars,
                            &mut applied_once,
                        )?;
                        let return_value = self.apply_set_bound_to_term_with_flag(
                            set_bound_scope_id,
                            case.return_value,
                            &new_ignore_bound_vars,
                            &mut applied_once,
                        )?;
                        Ok(TyFnCase { params, return_ty, return_value })
                    })
                    .collect::<TcResult<Vec<_>>>()?;

                if !applied_once {
                    Ok(None)
                } else {
                    Ok(Some(self.builder().create_term(Term::TyFn(TyFn {
                        general_params,
                        general_return_ty,
                        cases,
                        name: ty_fn.name,
                    }))))
                }
            }
            Term::TyFnTy(ty_fn_ty) => {
                // Same basic procedure as for TyFn.
                let ty_fn_ty = ty_fn_ty;
                let mut applied_once = false;
                let mut ty_fn_bound_vars_due_to_params = HashSet::new();
                self.add_param_vars_as_bound_vars_to_set(
                    ty_fn_ty.params,
                    &mut ty_fn_bound_vars_due_to_params,
                );
                let new_ignore_bound_vars = ignore_bound_vars
                    .union(&ty_fn_bound_vars_due_to_params)
                    .copied()
                    .collect::<HashSet<_>>();
                let params = self.apply_set_bound_to_params_with_flag(
                    set_bound_scope_id,
                    ty_fn_ty.params,
                    ignore_bound_vars,
                    &mut applied_once,
                )?;
                let return_ty = self.apply_set_bound_to_term_with_flag(
                    set_bound_scope_id,
                    ty_fn_ty.return_ty,
                    &new_ignore_bound_vars,
                    &mut applied_once,
                )?;
                if !applied_once {
                    Ok(None)
                } else {
                    Ok(Some(self.builder().create_ty_fn_ty_term(params, return_ty)))
                }
            }
            Term::TyFnCall(app_ty_fn) => {
                let app_ty_fn = app_ty_fn;
                let mut applied_once = false;
                let subject = self.apply_set_bound_to_term_with_flag(
                    set_bound_scope_id,
                    app_ty_fn.subject,
                    ignore_bound_vars,
                    &mut applied_once,
                )?;
                let args = self.apply_set_bound_to_args_with_flag(
                    set_bound_scope_id,
                    app_ty_fn.args,
                    ignore_bound_vars,
                    &mut applied_once,
                )?;
                if !applied_once {
                    Ok(None)
                } else {
                    Ok(Some(self.builder().create_app_ty_fn_term(subject, args)))
                }
            }
            Term::TyOf(term) => {
                let mut applied_once = false;
                let inner = self.apply_set_bound_to_term_with_flag(
                    set_bound_scope_id,
                    term,
                    ignore_bound_vars,
                    &mut applied_once,
                )?;
                if !applied_once {
                    Ok(None)
                } else {
                    Ok(Some(self.builder().create_ty_of_term(inner)))
                }
            }
            // Definite-level terms:
            Term::Level1(Level1Term::Tuple(tuple_ty)) => {
                let mut applied_once = false;
                let members = self.apply_set_bound_to_params_with_flag(
                    set_bound_scope_id,
                    tuple_ty.members,
                    ignore_bound_vars,
                    &mut applied_once,
                )?;
                if !applied_once {
                    Ok(None)
                } else {
                    Ok(Some(self.builder().create_tuple_ty_term(members)))
                }
            }
            Term::Level1(Level1Term::Fn(fn_ty)) => {
                let mut applied_once = false;
                let params = self.apply_set_bound_to_params_with_flag(
                    set_bound_scope_id,
                    fn_ty.params,
                    ignore_bound_vars,
                    &mut applied_once,
                )?;
                let return_ty = self.apply_set_bound_to_term_with_flag(
                    set_bound_scope_id,
                    fn_ty.return_ty,
                    ignore_bound_vars,
                    &mut applied_once,
                )?;
                if !applied_once {
                    Ok(None)
                } else {
                    Ok(Some(self.builder().create_fn_ty_term(params, return_ty)))
                }
            }
            Term::Level0(term) => match term {
                Level0Term::Rt(inner) => Ok(self
                    .apply_set_bound_to_term_rec(set_bound_scope_id, inner, ignore_bound_vars)?
                    .map(|result| self.builder().create_rt_term(result))),
                Level0Term::FnCall(fn_call) => {
                    let mut applied_once = false;
                    let subject = self.apply_set_bound_to_term_with_flag(
                        set_bound_scope_id,
                        fn_call.subject,
                        ignore_bound_vars,
                        &mut applied_once,
                    )?;
                    let args = self.apply_set_bound_to_args_with_flag(
                        set_bound_scope_id,
                        fn_call.args,
                        ignore_bound_vars,
                        &mut applied_once,
                    )?;
                    if !applied_once {
                        Ok(None)
                    } else {
                        Ok(Some(self.builder().create_fn_call_term(subject, args)))
                    }
                }
                Level0Term::FnLit(fn_lit) => {
                    let mut applied_once = false;
                    let fn_ty = self.apply_set_bound_to_term_with_flag(
                        set_bound_scope_id,
                        fn_lit.fn_ty,
                        ignore_bound_vars,
                        &mut applied_once,
                    )?;
                    let return_value = self.apply_set_bound_to_term_with_flag(
                        set_bound_scope_id,
                        fn_lit.return_value,
                        ignore_bound_vars,
                        &mut applied_once,
                    )?;
                    if !applied_once {
                        Ok(None)
                    } else {
                        Ok(Some(self.builder().create_fn_lit_term(fn_ty, return_value)))
                    }
                }
                Level0Term::EnumVariant(_) => {
                    // @@Remove: enum variants will be removed
                    Ok(None)
                }
                Level0Term::Tuple(tuple_lit) => {
                    let mut applied_once = false;
                    let members = self.apply_set_bound_to_args_with_flag(
                        set_bound_scope_id,
                        tuple_lit.members,
                        ignore_bound_vars,
                        &mut applied_once,
                    )?;
                    if !applied_once {
                        Ok(None)
                    } else {
                        Ok(Some(self.builder().create_tuple_lit_term(members)))
                    }
                }
                Level0Term::Lit(_) => Ok(None),
                Level0Term::Constructed(constructed) => {
                    let mut applied_once = false;
                    let subject = self.apply_set_bound_to_term_with_flag(
                        set_bound_scope_id,
                        constructed.subject,
                        ignore_bound_vars,
                        &mut applied_once,
                    )?;
                    let members = self.apply_set_bound_to_args_with_flag(
                        set_bound_scope_id,
                        constructed.members,
                        ignore_bound_vars,
                        &mut applied_once,
                    )?;
                    if !applied_once {
                        Ok(None)
                    } else {
                        Ok(Some(self.builder().create_constructed_term(subject, members)))
                    }
                }
                Level0Term::Unit(_) => Ok(None),
            },
            Term::Level1(Level1Term::ModDef(_))
            | Term::Level1(Level1Term::NominalDef(_))
            | Term::Level2(Level2Term::Trt(_))
            | Term::SetBound(_) => {
                let vars = self.get_free_bound_vars_in_term(term_id);
                if !self.scope_store().map_fast(set_bound_scope_id, |scope| {
                    scope.iter_names().any(|name| vars.contains(&BoundVar { name }))
                }) {
                    // No vars in mod:
                    Ok(None)
                } else {
                    // Wrap in set scope, filtered by having only the vars that appear in the term.
                    let filtered_set_bound_scope_id =
                        self.scope_manager().filter_scope(set_bound_scope_id, |member| {
                            vars.contains(&BoundVar { name: member.name() })
                        });
                    Ok(Some(
                        self.builder().create_set_bound_term(term_id, filtered_set_bound_scope_id),
                    ))
                }
            }
            Term::Level3(Level3Term::TrtKind)
            | Term::Level2(Level2Term::AnyTy)
            | Term::Level2(Level2Term::SizedTy)
            | Term::Var(_)
            | Term::Root
            | Term::ScopeVar(_)
            | Term::Unresolved(_) => {
                // Nothing to do:
                Ok(None)
            }
        }?;

        if let Some(result) = result {
            self.location_store().copy_location(term_id, result);
        }

        Ok(result)
    }
}
