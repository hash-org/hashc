//! Functionality related to discovering variables in terms.
use crate::storage::{
    primitives::{
        ArgsId, BoundVar, Level0Term, Level1Term, Level2Term, Level3Term, ParamsId, ScopeId, Sub,
        SubVar, Term, TermId,
    },
    AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
};
use std::collections::HashSet;

use super::AccessToOps;

/// Contains actions related to variable discovery.
pub struct Discoverer<'gs, 'ls, 'cd, 's> {
    storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for Discoverer<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}
impl<'gs, 'ls, 'cd, 's> AccessToStorageMut for Discoverer<'gs, 'ls, 'cd, 's> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 's> Discoverer<'gs, 'ls, 'cd, 's> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    /// Add the free variables in the parameter default values and types to the
    /// given [HashSet].
    pub fn add_free_sub_vars_in_params_to_set(
        &self,
        params_id: ParamsId,
        result: &mut HashSet<SubVar>,
    ) {
        let params = self.params_store().get(params_id);

        // Add default value and type free vars
        for param in params.positional() {
            self.add_free_sub_vars_in_term_to_set(param.ty, result);
            if let Some(default_value_id) = param.default_value {
                self.add_free_sub_vars_in_term_to_set(default_value_id, result);
            }
        }
    }

    /// Add the free variables that exist in the given args, to the given
    /// [HashSet].
    pub fn add_free_sub_vars_in_args_to_set(&self, args_id: ArgsId, result: &mut HashSet<SubVar>) {
        let args = self.args_store().get(args_id);

        for arg in args.positional() {
            self.add_free_sub_vars_in_term_to_set(arg.value, result);
        }
    }

    /// Add the free variables that exist in the given [Level0Term], to the
    /// given [HashSet].
    pub fn add_free_sub_vars_in_level0_term_to_set(
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
            Level0Term::EnumVariant(_) | Level0Term::Lit(_) => {}
        }
    }

    /// Add the free variables that exist in the given [Level1Term], to the
    /// given [HashSet].
    pub fn add_free_sub_vars_in_level1_term_to_set(
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

    /// Add the free variables that exist in the given [Level2Term], to the
    /// given [HashSet].
    pub fn add_free_sub_vars_in_level2_term_to_set(
        &self,
        term: &Level2Term,
        _result: &mut HashSet<SubVar>,
    ) {
        match term {
            Level2Term::Trt(_) | Level2Term::AnyTy => {}
        }
    }

    /// Add the free variables that exist in the given [Level3Term], to the
    /// given [HashSet].
    pub fn add_free_sub_vars_in_level3_term_to_set(
        &self,
        term: &Level3Term,
        _: &mut HashSet<SubVar>,
    ) {
        match term {
            Level3Term::TrtKind => {}
        }
    }

    /// Add the free variables that exist in the given term, to the given
    /// [HashSet].
    ///
    /// Free variables are either `Var` or `Unresolved`, and this function
    /// collects both.
    pub fn add_free_sub_vars_in_term_to_set(&self, term_id: TermId, result: &mut HashSet<SubVar>) {
        let reader = self.reader();
        let term = reader.get_term(term_id);
        match term {
            Term::Unresolved(unresolved) => {
                // Found a free variable:
                result.insert((*unresolved).into());
            }
            Term::Access(term) => {
                // Free vars in the subject:
                self.add_free_sub_vars_in_term_to_set(term.subject, result);
            }
            Term::Merge(terms) => {
                // Free vars in each term:
                for inner_term_id in terms {
                    self.add_free_sub_vars_in_term_to_set(*inner_term_id, result);
                }
            }
            Term::Union(terms) => {
                // Free vars in each term:
                for inner_term_id in terms {
                    self.add_free_sub_vars_in_term_to_set(*inner_term_id, result);
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
                self.add_free_sub_vars_in_term_to_set(*term, result);
            }
            // Definite-level terms:
            Term::Level3(term) => {
                self.add_free_sub_vars_in_level3_term_to_set(term, result);
            }
            Term::Level2(term) => {
                self.add_free_sub_vars_in_level2_term_to_set(term, result);
            }
            Term::Level1(term) => {
                self.add_free_sub_vars_in_level1_term_to_set(term, result);
            }
            Term::Level0(term) => {
                self.add_free_sub_vars_in_level0_term_to_set(term, result);
            }
            // No vars:
            Term::Var(_) | Term::Root | Term::ScopeVar(_) | Term::BoundVar(_) => {}
        }
    }

    /// Add the free variables that exist in the given [Sub], to the
    /// given [HashSet].
    pub fn add_free_sub_vars_in_sub_to_set(&self, sub: &Sub, result: &mut HashSet<SubVar>) {
        // Add all the variables in the range, minus the variables in the domain:
        for r in sub.range() {
            self.add_free_sub_vars_in_term_to_set(r, result);
        }
        let mut domain_vars = HashSet::new();
        for d in sub.range() {
            self.add_free_sub_vars_in_term_to_set(d, &mut domain_vars);
        }
        // Remove all the variables in domain_vars:
        for d in domain_vars {
            result.remove(&d);
        }
    }

    /// Get the free variables that exist in the given [Sub].
    pub fn get_free_sub_vars_in_sub(&self, sub: &Sub) -> HashSet<SubVar> {
        let mut result = HashSet::new();
        self.add_free_sub_vars_in_sub_to_set(sub, &mut result);
        result
    }

    /// Get the set of free variables that exist in the given term.
    ///
    /// Free variables are either `Var` or `Unresolved`, and this function
    /// collects both.
    pub fn get_free_sub_vars_in_term(&self, term_id: TermId) -> HashSet<SubVar> {
        let mut result = HashSet::new();
        self.add_free_sub_vars_in_term_to_set(term_id, &mut result);
        result
    }

    /// Add the free variables in the parameter default values and types to the
    /// given [HashSet].
    pub fn add_free_bound_vars_in_params_to_set(
        &self,
        params_id: ParamsId,
        result: &mut HashSet<BoundVar>,
    ) {
        let params = self.params_store().get(params_id);

        // Add default value and type free vars
        for param in params.positional() {
            self.add_free_bound_vars_in_term_to_set(param.ty, result);
            if let Some(default_value_id) = param.default_value {
                self.add_free_bound_vars_in_term_to_set(default_value_id, result);
            }
        }
    }

    /// Add the parameter variables in the parameters to the given [HashSet] as
    /// [BoundVar]s.
    pub fn add_param_vars_as_bound_vars_to_set(
        &self,
        params_id: ParamsId,
        result: &mut HashSet<BoundVar>,
    ) {
        let params = self.params_store().get(params_id);

        // Add default value and type free vars
        for param in params.positional() {
            if let Some(name) = param.name {
                result.insert(BoundVar { name });
            }
        }
    }

    /// Add the free variables that exist in the given args, to the given
    /// [HashSet].
    pub fn add_free_bound_vars_in_args_to_set(
        &self,
        args_id: ArgsId,
        result: &mut HashSet<BoundVar>,
    ) {
        let args = self.args_store().get(args_id);

        for arg in args.positional() {
            self.add_free_bound_vars_in_term_to_set(arg.value, result);
        }
    }

    /// Add the free variables that exist in the given [Level0Term], to the
    /// given [HashSet].
    pub fn add_free_bound_vars_in_level0_term_to_set(
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
            Level0Term::EnumVariant(_) | Level0Term::Lit(_) => {}
        }
    }

    /// Add the free variables that exist in the given [Level1Term], to the
    /// given [HashSet].
    pub fn add_free_bound_vars_in_level1_term_to_set(
        &self,
        term: &Level1Term,
        result: &mut HashSet<BoundVar>,
    ) {
        match term {
            Level1Term::ModDef(_) | Level1Term::NominalDef(_) => {}
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

    /// Add the free variables that exist in the given [Level2Term], to the
    /// given [HashSet].
    pub fn add_free_bound_vars_in_level2_term_to_set(
        &self,
        term: &Level2Term,
        _result: &mut HashSet<BoundVar>,
    ) {
        match term {
            Level2Term::Trt(_) | Level2Term::AnyTy => {}
        }
    }

    /// Add the free variables that exist in the given [Level3Term], to the
    /// given [HashSet].
    pub fn add_free_bound_vars_in_level3_term_to_set(
        &self,
        term: &Level3Term,
        _: &mut HashSet<BoundVar>,
    ) {
        match term {
            Level3Term::TrtKind => {}
        }
    }

    /// Add the free variables that exist in the given [ScopeId], to the
    /// given [HashSet].
    ///
    /// This adds the free (bound) variables in the member types and values.
    pub fn add_free_bound_vars_in_scope_to_set(
        &self,
        scope: ScopeId,
        result: &mut HashSet<BoundVar>,
    ) {
        let reader = self.reader();
        let scope = reader.get_scope(scope);
        for member in scope.iter() {
            if let Some(ty) = member.data.ty() {
                self.add_free_bound_vars_in_term_to_set(ty, result)
            }
            if let Some(value) = member.data.value() {
                self.add_free_bound_vars_in_term_to_set(value, result)
            }
        }
    }

    /// Add the free variables that exist in the given term, to the given
    /// [HashSet].
    ///
    /// Free variables are either `Var` or `Unresolved`, and this function
    /// collects both.
    pub fn add_free_bound_vars_in_term_to_set(
        &self,
        term_id: TermId,
        result: &mut HashSet<BoundVar>,
    ) {
        let reader = self.reader();
        let term = reader.get_term(term_id);
        match term {
            Term::BoundVar(var) => {
                // Found a bound var
                result.insert(*var);
            }
            Term::Access(term) => {
                // Free vars in the subject:
                self.add_free_bound_vars_in_term_to_set(term.subject, result);
            }
            Term::Merge(terms) => {
                // Free vars in each term:
                for inner_term_id in terms {
                    self.add_free_bound_vars_in_term_to_set(*inner_term_id, result);
                }
            }
            Term::Union(terms) => {
                // Free vars in each term:
                for inner_term_id in terms {
                    self.add_free_bound_vars_in_term_to_set(*inner_term_id, result);
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
                self.add_free_bound_vars_in_term_to_set(*term, result);
            }
            // Definite-level terms:
            Term::Level3(term) => {
                self.add_free_bound_vars_in_level3_term_to_set(term, result);
            }
            Term::Level2(term) => {
                self.add_free_bound_vars_in_level2_term_to_set(term, result);
            }
            Term::Level1(term) => {
                self.add_free_bound_vars_in_level1_term_to_set(term, result);
            }
            Term::Level0(term) => {
                self.add_free_bound_vars_in_level0_term_to_set(term, result);
            }
            // No bound vars:
            Term::Var(_) | Term::Root | Term::ScopeVar(_) | Term::Unresolved(_) => {}
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
}
