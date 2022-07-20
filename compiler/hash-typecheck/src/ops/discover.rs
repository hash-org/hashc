//! Functionality related to discovering variables in terms.
use std::collections::HashSet;

use hash_source::identifier::CORE_IDENTIFIERS;

use crate::{
    diagnostics::error::{TcError, TcResult},
    storage::{
        primitives::{
            ArgsId, Level0Term, Level1Term, Level2Term, Level3Term, ParamsId, Sub, SubSubject,
            Term, TermId, Var,
        },
        AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
    },
};

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
    pub fn add_free_vars_in_params_to_set(
        &self,
        params_id: ParamsId,
        result: &mut HashSet<SubSubject>,
    ) {
        let params = self.params_store().get(params_id);

        // Add default value and type free vars
        for param in params.positional() {
            self.add_free_vars_in_term_to_set(param.ty, result);
            if let Some(default_value_id) = param.default_value {
                self.add_free_vars_in_term_to_set(default_value_id, result);
            }
        }
    }

    /// Remove the free variables that exist in the given params as names, from
    /// the given [HashSet], and add the free variables in the default
    /// values and types.
    ///
    /// This is to be used for type functions.
    pub fn add_and_remove_free_vars_in_params_from_set(
        &self,
        _params_id: ParamsId,
        _result: &mut HashSet<SubSubject>,
    ) {
        // self.add_free_vars_in_params_to_set(params_id, result);

        // let params = self.params_store().get(params_id);
        // // Remove param names
        // for param in params.positional() {
        //     if let Some(name) = param.name {
        //         let subject = Var { name };
        //         result.remove(&subject.into());
        //     }
        // }
        todo!()
    }

    /// Add the free variables that exist in the given args, to the given
    /// [HashSet].
    pub fn add_free_vars_in_args_to_set(&self, args_id: ArgsId, result: &mut HashSet<SubSubject>) {
        let args = self.args_store().get(args_id);

        for arg in args.positional() {
            self.add_free_vars_in_term_to_set(arg.value, result);
        }
    }

    /// Add the free variables that exist in the given [Level0Term], to the
    /// given [HashSet].
    pub fn add_free_vars_in_level0_term_to_set(
        &self,
        term: &Level0Term,
        result: &mut HashSet<SubSubject>,
    ) {
        match term {
            Level0Term::Rt(ty_term_id) => self.add_free_vars_in_term_to_set(*ty_term_id, result),
            Level0Term::EnumVariant(enum_variant) => {
                // Forward to the nominal enum definition
                let enum_def = Level1Term::NominalDef(enum_variant.enum_def_id);
                self.add_free_vars_in_level1_term_to_set(&enum_def, result);
            }
            Level0Term::FnLit(fn_lit) => {
                // Forward to fn type and return value
                self.add_free_vars_in_term_to_set(fn_lit.fn_ty, result);
                self.add_free_vars_in_term_to_set(fn_lit.return_value, result);
            }
            Level0Term::FnCall(fn_call) => {
                // Forward to subject and args:
                self.add_free_vars_in_term_to_set(fn_call.subject, result);
                self.add_free_vars_in_args_to_set(fn_call.args, result);
            }
            Level0Term::Tuple(tuple_lit) => {
                self.add_free_vars_in_args_to_set(tuple_lit.members, result);
            }
            Level0Term::Lit(_) => {}
        }
    }

    /// Add the free variables that exist in the given [Level1Term], to the
    /// given [HashSet].
    pub fn add_free_vars_in_level1_term_to_set(
        &self,
        term: &Level1Term,
        result: &mut HashSet<SubSubject>,
    ) {
        match term {
            Level1Term::ModDef(_mod_def_id) => {
                // Add the bound vars of the module (they are not bound because they are not
                // behind a type function anymore).
                // result.extend(
                //     self.reader()
                //         .get_mod_def(*mod_def_id)
                //         .bound_vars
                //         .iter()
                //         .copied()
                //         .map(SubSubject::from),
                // )
                todo!()
            }
            Level1Term::NominalDef(_nominal_def_id) => {
                // Add the bound vars of the nominal definition (they are not bound because they
                // are not behind a type function anymore).
                // result.extend(
                //     self.reader()
                //         .get_nominal_def(*nominal_def_id)
                //         .bound_vars()
                //         .iter()
                //         .copied()
                //         .map(SubSubject::from),
                // )
                todo!()
            }
            Level1Term::Tuple(tuple_ty) => {
                // Add the free variables in the parameters (don't remove the parameter names)
                self.add_free_vars_in_params_to_set(tuple_ty.members, result);
            }
            Level1Term::Fn(fn_ty) => {
                // Add the free variables in the parameters and return type.
                self.add_free_vars_in_params_to_set(fn_ty.params, result);
                self.add_free_vars_in_term_to_set(fn_ty.return_ty, result);
            }
        }
    }

    /// Add the free variables that exist in the given [Level2Term], to the
    /// given [HashSet].
    pub fn add_free_vars_in_level2_term_to_set(
        &self,
        term: &Level2Term,
        _result: &mut HashSet<SubSubject>,
    ) {
        match term {
            Level2Term::Trt(_trt_def_id) => {
                // Add the bound vars of the trait definition (they are not bound because they
                // are not behind a type function anymore).
                // result.extend(
                //     self.reader()
                //         .get_trt_def(*trt_def_id)
                //         .bound_vars
                //         .iter()
                //         .copied()
                //         .map(SubSubject::from),
                // )
                todo!()
            }
            Level2Term::AnyTy => {}
        }
    }

    /// Add the free variables that exist in the given [Level3Term], to the
    /// given [HashSet].
    pub fn add_free_vars_in_level3_term_to_set(
        &self,
        term: &Level3Term,
        _: &mut HashSet<SubSubject>,
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
    pub fn add_free_vars_in_term_to_set(&self, term_id: TermId, result: &mut HashSet<SubSubject>) {
        let reader = self.reader();
        let term = reader.get_term(term_id);
        match term {
            Term::Var(_var) => {
                // Found a free variable:
                // @@Correctness: what if this is bound in the scope?
                // result.insert((*var).into());
                todo!()
            }
            Term::BoundVar(_) => todo!(),
            Term::Unresolved(unresolved) => {
                // Found an unresolved free variable:
                result.insert((*unresolved).into());
            }
            Term::Access(term) => {
                // Just the free vars in the subject:
                self.add_free_vars_in_term_to_set(term.subject, result);
            }
            Term::Merge(terms) => {
                // Free vars in each term:
                for inner_term_id in terms {
                    self.add_free_vars_in_term_to_set(*inner_term_id, result);
                }
            }
            Term::Union(terms) => {
                // Free vars in each term:
                for inner_term_id in terms {
                    self.add_free_vars_in_term_to_set(*inner_term_id, result);
                }
            }
            Term::TyFn(ty_fn) => {
                // Add the vars in the subjects and return:
                self.add_free_vars_in_term_to_set(ty_fn.general_return_ty, result);
                for case in &ty_fn.cases {
                    self.add_free_vars_in_term_to_set(case.return_ty, result);
                    self.add_free_vars_in_term_to_set(case.return_value, result);
                }

                // Remove the ones which are bound:
                self.add_and_remove_free_vars_in_params_from_set(ty_fn.general_params, result);
                // And from the cases:
                for case in &ty_fn.cases {
                    // @@Correctness: is this right? is it necessary?
                    self.add_and_remove_free_vars_in_params_from_set(case.params, result);
                }
            }
            Term::TyFnTy(ty_fn_ty) => {
                // Add the vars in the subjects and return:
                self.add_free_vars_in_term_to_set(ty_fn_ty.return_ty, result);

                // Remove the ones which are bound:
                self.add_and_remove_free_vars_in_params_from_set(ty_fn_ty.params, result);
            }
            Term::TyFnCall(app_ty_fn) => {
                // Free vars in subject and args
                self.add_free_vars_in_term_to_set(app_ty_fn.subject, result);
                self.add_free_vars_in_args_to_set(app_ty_fn.args, result);
            }
            Term::SetBound(_app_sub) => {
                // Add free vars in the subject term
                // self.add_free_vars_in_term_to_set(app_sub.term, result);

                // // Remove free vars in the domain of the substitution
                // for var in app_sub.sub.domain() {
                //     result.remove(&var);
                // }

                // // Add free vars in the range of the substitution
                // for range_el in app_sub.sub.range() {
                //     self.add_free_vars_in_term_to_set(range_el, result);
                // }
                todo!()
            }
            Term::TyOf(term) => {
                // Add free vars in the inner term
                self.add_free_vars_in_term_to_set(*term, result);
            }
            // Definite-level terms:
            Term::Level3(term) => {
                self.add_free_vars_in_level3_term_to_set(term, result);
            }
            Term::Level2(term) => {
                self.add_free_vars_in_level2_term_to_set(term, result);
            }
            Term::Level1(term) => {
                self.add_free_vars_in_level1_term_to_set(term, result);
            }
            Term::Level0(term) => {
                self.add_free_vars_in_level0_term_to_set(term, result);
            }
            // No vars:
            Term::Root => {}
            Term::ScopeVar(_) => todo!(),
        }
    }

    /// Add the free variables that exist in the given [Sub], to the
    /// given [HashSet].
    pub fn add_free_vars_in_sub_to_set(&self, sub: &Sub, result: &mut HashSet<SubSubject>) {
        // Add all the variables in the range, minus the variables in the domain:
        for r in sub.range() {
            self.add_free_vars_in_term_to_set(r, result);
        }
        let mut domain_vars = HashSet::new();
        for d in sub.range() {
            self.add_free_vars_in_term_to_set(d, &mut domain_vars);
        }
        // Remove all the variables in domain_vars:
        for d in domain_vars {
            result.remove(&d);
        }
    }

    /// Get the free variables that exist in the given [Sub].
    pub fn get_free_vars_in_sub(&self, sub: &Sub) -> HashSet<SubSubject> {
        let mut result = HashSet::new();
        self.add_free_vars_in_sub_to_set(sub, &mut result);
        result
    }

    /// Get the set of free variables that exist in the given term.
    ///
    /// Free variables are either `Var` or `Unresolved`, and this function
    /// collects both.
    pub fn get_free_vars_in_term(&self, term_id: TermId) -> HashSet<SubSubject> {
        let mut result = HashSet::new();
        self.add_free_vars_in_term_to_set(term_id, &mut result);
        result
    }

    /// Get the set of variables that exist in the given term. This function
    /// will proceed an error if it hits an un-resolved free variable since this
    /// cannot appear within certain contexts, e.g. nominal definitions.
    pub fn discover_free_vars_in_term(&self, term_id: TermId) -> TcResult<HashSet<Var>> {
        let mut result = HashSet::new();
        self.add_free_vars_in_term_to_set(term_id, &mut result);

        result
            .into_iter()
            .map(|var| match var {
                SubSubject::Unresolved(_) => Err(TcError::UnresolvedVariable {
                    // @@Correctness: it's unclear if we can even get an identifier here? Or if we
                    // should make an identifier from the provided `ResolutionId`
                    name: CORE_IDENTIFIERS.underscore,
                    value: term_id,
                }),
            })
            .collect::<TcResult<_>>()
    }
}
