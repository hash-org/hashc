//! Functionality related to variable substitution inside terms/types.
use crate::storage::{
    primitives::{
        AppSub, AppTyFn, Arg, ArgsId, FnTy, Level0Term, Level1Term, Level2Term, Level3Term, Param,
        ParamsId, Sub, SubSubject, Term, TermId, TupleTy, TyFn, TyFnCase, TyFnTy, Var,
    },
    AccessToStorage, AccessToStorageMut, StorageRefMut,
};
use std::collections::{HashMap, HashSet};

use super::{AccessToOps, AccessToOpsMut};

/// Can perform substitutions (see [Sub]) on terms.
pub struct Substituter<'gs, 'ls, 'cd> {
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for Substituter<'gs, 'ls, 'cd> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> AccessToStorageMut for Substituter<'gs, 'ls, 'cd> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd> Substituter<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    /// Apply the given substitution to the given arguments, producing a new set
    /// of arguments with the substituted variables.
    pub fn apply_sub_to_args(&mut self, sub: &Sub, args_id: ArgsId) -> ArgsId {
        let args = self.args_store().get(args_id).clone();

        let new_args = args
            .positional()
            .iter()
            .map(|arg| Arg { name: arg.name, value: self.apply_sub_to_term(sub, arg.value) })
            .collect::<Vec<_>>();

        self.builder().create_args(new_args)
    }

    /// Apply the given substitution to the given parameters, producing a new
    /// set of parameters with the substituted variables.
    pub fn apply_sub_to_params(&mut self, sub: &Sub, params_id: ParamsId) -> ParamsId {
        let params = self.params_store().get(params_id).clone();

        let new_params = params
            .positional()
            .iter()
            .map(|param| Param {
                name: param.name,
                ty: self.apply_sub_to_term(sub, param.ty),
                default_value: param.default_value.map(|value| self.apply_sub_to_term(sub, value)),
            })
            .collect::<Vec<_>>();

        self.builder().create_params(new_params)
    }

    /// Apply the given substitution to the given [Level3Term], producing a new
    /// [Level3Term] with the substituted variables.
    pub fn apply_sub_to_level3_term(&mut self, _: &Sub, term: Level3Term) -> TermId {
        match term {
            Level3Term::TrtKind => self.builder().create_term(Term::Level3(Level3Term::TrtKind)),
        }
    }

    /// Apply the given substitution to the given [Level2Term], producing a new
    /// [Level2Term] with the substituted variables.
    pub fn apply_sub_to_level2_term(&mut self, sub: &Sub, term: Level2Term) -> TermId {
        match term {
            Level2Term::Trt(trt_def_id) => {
                // Here we add the substitution to the term using only vars in the trait
                // definition.
                let reader = self.reader();
                let trt_def_vars = &reader.get_trt_def(trt_def_id).bound_vars;
                let selected_sub = sub.select(trt_def_vars);
                let builder = self.builder();
                builder.create_app_sub_term(selected_sub, builder.create_term(Term::Level2(term)))
            }
            Level2Term::AnyTy => (self.builder().create_term(Term::Level2(Level2Term::AnyTy))),
        }
    }

    /// Apply the given substitution to the given [Level1Term], producing a new
    /// [Level1Term] with the substituted variables.
    pub fn apply_sub_to_level1_term(&mut self, sub: &Sub, term: Level1Term) -> TermId {
        match term {
            Level1Term::ModDef(mod_def_id) => {
                // Here we add the substitution to the term using only vars in the mod
                // definition.
                let reader = self.reader();
                let mod_def_vars = &reader.get_mod_def(mod_def_id).bound_vars;
                let selected_sub = sub.select(mod_def_vars);
                let builder = self.builder();
                builder.create_app_sub_term(selected_sub, builder.create_term(Term::Level1(term)))
            }
            Level1Term::NominalDef(nominal_def_id) => {
                // Here we add the substitution to the term using only vars in the nominal
                // definition.
                let reader = self.reader();
                let nominal_def_vars = reader.get_nominal_def(nominal_def_id).bound_vars();
                let selected_sub = sub.select(nominal_def_vars);
                let builder = self.builder();
                builder.create_app_sub_term(selected_sub, builder.create_term(Term::Level1(term)))
            }
            Level1Term::Tuple(tuple_ty) => {
                // Apply to all members
                let subbed_members = self.apply_sub_to_params(sub, tuple_ty.members);
                self.builder().create_term(Term::Level1(Level1Term::Tuple(TupleTy {
                    members: subbed_members,
                })))
            }
            Level1Term::Fn(fn_ty) => {
                // Apply to parameters and return type
                let subbed_params = self.apply_sub_to_params(sub, fn_ty.params);
                let subbed_return_ty = self.apply_sub_to_term(sub, fn_ty.return_ty);
                self.builder().create_term(Term::Level1(Level1Term::Fn(FnTy {
                    params: subbed_params,
                    return_ty: subbed_return_ty,
                })))
            }
        }
    }

    /// Apply the given substitution to the given [Level0Term], producing a new
    /// [Level0Term] with the substituted variables.
    pub fn apply_sub_to_level0_term(&mut self, sub: &Sub, term: Level0Term) -> TermId {
        match term {
            Level0Term::Rt(ty_term_id) => {
                // Apply to the type of the runtime value
                let subbed_ty_term_id = self.apply_sub_to_term(sub, ty_term_id);
                self.builder().create_rt_term(subbed_ty_term_id)
            }
            Level0Term::EnumVariant(enum_variant) => {
                // Here we add the substitution to the term using only vars in the enum
                // definition.
                let reader = self.reader();
                let enum_def_vars = reader.get_nominal_def(enum_variant.enum_def_id).bound_vars();
                let selected_sub = sub.select(enum_def_vars);
                let builder = self.builder();
                builder.create_app_sub_term(
                    selected_sub,
                    builder.create_term(Term::Level0(Level0Term::EnumVariant(enum_variant))),
                )
            }
            Level0Term::FnLit(fn_lit) => {
                // Apply to the function type and return value
                let subbed_fn_ty = self.apply_sub_to_term(sub, fn_lit.fn_ty);
                let subbed_return_value = self.apply_sub_to_term(sub, fn_lit.return_value);
                self.builder().create_fn_lit_term(subbed_fn_ty, subbed_return_value)
            }
        }
    }

    /// Apply the given substitution to the given [SubSubject], producing a new
    /// term with the substituted result.
    pub fn apply_sub_to_subject(&mut self, sub: &Sub, subject: SubSubject) -> TermId {
        match sub.get_sub_for(subject) {
            Some(subbed_term_id) => subbed_term_id,
            None => self.builder().create_term(subject.into()),
        }
    }

    /// Apply the given substitution to the term indexed by the given [TermId],
    /// producing a new term with the substituted variables.
    ///
    /// Sometimes, this will actually create a [Term::AppSub] somewhere inside
    /// the term tree, and those are the leaf nodes of the substitution
    /// application. This will happen with `ModDef`, `TrtDef`, `NominalDef`,
    /// and `EnumVariant`. This is so that when `AccessTerm` is resolved for
    /// those types, the substitution is carried forward into the member term.
    pub fn apply_sub_to_term(&mut self, sub: &Sub, term_id: TermId) -> TermId {
        // @@Performance: here we copy a lot, maybe there is a way to avoid all this
        // copying by first checking that the variables to be substituted
        // actually exist in the term.

        let term = self.reader().get_term(term_id).clone();

        let new_term = match term {
            // Leaves:
            Term::Var(var) => self.apply_sub_to_subject(sub, var.into()),
            Term::Unresolved(unresolved) => self.apply_sub_to_subject(sub, unresolved.into()),
            Term::Root => term_id,

            // Recursive cases:
            Term::Access(access) => {
                // Just apply the substitution to the subject:
                let subbed_subject_id = self.apply_sub_to_term(sub, access.subject);
                self.builder().create_ns_access(subbed_subject_id, access.name)
            }
            Term::Merge(terms) => {
                // Apply the substitution to each element of the merge.
                let terms = terms
                    .into_iter()
                    .map(|term| self.apply_sub_to_term(sub, term))
                    .collect::<Vec<_>>();
                self.builder().create_term(Term::Merge(terms))
            }
            Term::TyFn(ty_fn) => {
                // Apply the substitution to the general parameters, return type, and each case.
                //
                // However, we first have to remove all the shadowed variables from the
                // substitution: If we have T -> str, and <T> => List<T>, we
                // don't wanna get <T> => List<str> because T is bound in the
                // term, not free.
                let params = self.params_store().get(ty_fn.general_params).clone();

                let shadowed_sub = sub.filter(params);
                let subbed_general_params =
                    self.apply_sub_to_params(&shadowed_sub, ty_fn.general_params);
                let subbed_general_return_ty =
                    self.apply_sub_to_term(&shadowed_sub, ty_fn.general_return_ty);

                let subbed_cases = ty_fn
                    .cases
                    .into_iter()
                    .map(|case| TyFnCase {
                        params: self.apply_sub_to_params(&shadowed_sub, case.params),
                        return_ty: self.apply_sub_to_term(&shadowed_sub, case.return_ty),
                        return_value: self.apply_sub_to_term(&shadowed_sub, case.return_value),
                    })
                    .collect::<Vec<_>>();
                self.builder().create_term(Term::TyFn(TyFn {
                    name: ty_fn.name,
                    general_params: subbed_general_params,
                    general_return_ty: subbed_general_return_ty,
                    cases: subbed_cases,
                }))
            }
            Term::TyFnTy(ty_fn_ty) => {
                // Apply the substitution to the parameters and return type.
                // Same rule applies about binding as above.
                let params = self.params_store().get(ty_fn_ty.params).clone();

                let shadowed_sub = sub.filter(params);
                let subbed_params = self.apply_sub_to_params(&shadowed_sub, ty_fn_ty.params);
                let subbed_return_ty = self.apply_sub_to_term(&shadowed_sub, ty_fn_ty.return_ty);
                self.builder().create_term(Term::TyFnTy(TyFnTy {
                    params: subbed_params,
                    return_ty: subbed_return_ty,
                }))
            }
            Term::AppTyFn(app_ty_fn) => {
                // Apply the substitution to the subject and arguments.
                let subbed_subject = self.apply_sub_to_term(sub, app_ty_fn.subject);
                let subbed_args = self.apply_sub_to_args(sub, app_ty_fn.args);
                self.builder().create_term(Term::AppTyFn(AppTyFn {
                    subject: subbed_subject,
                    args: subbed_args,
                }))
            }
            Term::AppSub(app_sub) => {
                // @@Correctness: do we not want to unify substitutions here?
                //
                // Here, we have to substitute all X in * -> X pairs of the substitution, as
                // well as the subject term itself.
                let subbed_sub = app_sub
                    .sub
                    .pairs()
                    .map(|(from, to)| (from, self.apply_sub_to_term(sub, to)))
                    .collect::<HashMap<_, _>>();
                let subbed_term = self.apply_sub_to_term(sub, app_sub.term);
                self.builder().create_term(Term::AppSub(AppSub {
                    sub: Sub::from_map(subbed_sub),
                    term: subbed_term,
                }))
            }
            // Definite-level terms:
            Term::Level3(term) => self.apply_sub_to_level3_term(sub, term),
            Term::Level2(term) => self.apply_sub_to_level2_term(sub, term),
            Term::Level1(term) => self.apply_sub_to_level1_term(sub, term),
            Term::Level0(term) => self.apply_sub_to_level0_term(sub, term),
        };

        self.location_store_mut().copy_location(term_id, new_term);
        new_term
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
        params_id: ParamsId,
        result: &mut HashSet<SubSubject>,
    ) {
        self.add_free_vars_in_params_to_set(params_id, result);

        let params = self.params_store().get(params_id);
        // Remove param names
        for param in params.positional() {
            if let Some(name) = param.name {
                let subject = Var { name };
                result.remove(&subject.into());
            }
        }
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
            Level1Term::ModDef(mod_def_id) => {
                // Add the bound vars of the module (they are not bound because they are not
                // behind a type function anymore).
                result.extend(
                    self.reader()
                        .get_mod_def(*mod_def_id)
                        .bound_vars
                        .iter()
                        .copied()
                        .map(SubSubject::from),
                )
            }
            Level1Term::NominalDef(nominal_def_id) => {
                // Add the bound vars of the nominal definition (they are not bound because they
                // are not behind a type function anymore).
                result.extend(
                    self.reader()
                        .get_nominal_def(*nominal_def_id)
                        .bound_vars()
                        .iter()
                        .copied()
                        .map(SubSubject::from),
                )
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
        result: &mut HashSet<SubSubject>,
    ) {
        match term {
            Level2Term::Trt(trt_def_id) => {
                // Add the bound vars of the trait definition (they are not bound because they
                // are not behind a type function anymore).
                result.extend(
                    self.reader()
                        .get_trt_def(*trt_def_id)
                        .bound_vars
                        .iter()
                        .copied()
                        .map(SubSubject::from),
                )
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
            Term::Var(var) => {
                // Found a free variable:
                // @@Correctness: what if this is bound in the scope?
                result.insert((*var).into());
            }
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
            Term::AppTyFn(app_ty_fn) => {
                // Free vars in subject and args
                self.add_free_vars_in_term_to_set(app_ty_fn.subject, result);
                self.add_free_vars_in_args_to_set(app_ty_fn.args, result);
            }
            Term::AppSub(app_sub) => {
                // Add free vars in the subject term
                self.add_free_vars_in_term_to_set(app_sub.term, result);

                // Remove free vars in the domain of the substitution
                for var in app_sub.sub.domain() {
                    result.remove(&var);
                }

                // Add free vars in the range of the substitution
                for range_el in app_sub.sub.range() {
                    self.add_free_vars_in_term_to_set(range_el, result);
                }
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
        }
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
}

#[cfg(test)]
mod tests {
    use super::Substituter;
    use crate::{
        fmt::PrepareForFormatting,
        ops::AccessToOpsMut,
        storage::{
            core::CoreDefs,
            primitives::{ModDefOrigin, Sub},
            AccessToStorage, AccessToStorageMut, GlobalStorage, LocalStorage, StorageRefMut,
        },
    };

    #[test]
    fn test_substitutions() {
        let mut global_storage = GlobalStorage::new();
        let mut local_storage = LocalStorage::new(&mut global_storage);
        let core_defs = CoreDefs::new(&mut global_storage);
        let mut storage_ref = StorageRefMut {
            core_defs: &core_defs,
            global_storage: &mut global_storage,
            local_storage: &mut local_storage,
        };

        let builder = storage_ref.builder();

        // Visual testing for now, until term unification is implemented and we can
        // actually write proper tests here:
        let hash_impl = builder.create_nameless_mod_def(
            ModDefOrigin::TrtImpl(builder.create_trt_term(core_defs.hash_trt)),
            builder.create_constant_scope([]),
            [],
        );

        let inner = builder.create_nameless_ty_fn_term(
            builder.create_params([builder.create_param("T", builder.create_any_ty_term())]),
            builder.create_any_ty_term(),
            builder.create_app_ty_fn_term(
                core_defs.set_ty_fn,
                builder.create_args([
                    builder.create_arg("T", builder.create_var_term("T")),
                    builder.create_arg("X", builder.create_mod_def_term(hash_impl)),
                ]),
            ),
        );
        let target = builder.create_ty_fn_ty_term(
            builder.create_params([builder.create_param("U", builder.create_any_ty_term())]),
            builder.create_fn_ty_term(
                builder.create_params([
                    builder.create_param("foo", builder.create_unresolved_term()),
                    builder.create_param(
                        "bar",
                        builder.create_app_ty_fn_term(
                            core_defs.list_ty_fn,
                            builder.create_args([builder.create_arg("T", inner)]),
                        ),
                    ),
                ]),
                builder.create_var_term("T"),
            ),
        );

        println!();

        println!("{}", target.for_formatting(storage_ref.global_storage()));

        let builder = storage_ref.builder();
        let sub = Sub::from_pairs([(
            builder.create_var("T"),
            builder.create_app_ty_fn_term(
                core_defs.map_ty_fn,
                builder.create_args([
                    builder.create_arg("K", builder.create_nominal_def_term(core_defs.str_ty)),
                    builder.create_arg("V", builder.create_nominal_def_term(core_defs.u64_ty)),
                ]),
            ),
        )]);

        let mut substituter = Substituter::new(storage_ref.storages_mut());
        let subbed_target = substituter.apply_sub_to_term(&sub, target);

        let target_free_vars = substituter.get_free_vars_in_term(target);
        let inner_free_vars = substituter.get_free_vars_in_term(inner);

        let target_free_vars_list: Vec<_> = target_free_vars
            .into_iter()
            .map(|x| storage_ref.builder().create_term(x.into()))
            .collect();

        let inner_free_vars_list: Vec<_> = inner_free_vars
            .into_iter()
            .map(|x| storage_ref.builder().create_term(x.into()))
            .collect();

        println!("{}", subbed_target.for_formatting(storage_ref.global_storage()));

        print!("\nTarget free vars:\n");
        for target_free_var in &target_free_vars_list {
            println!("{}", target_free_var.for_formatting(storage_ref.global_storage()));
        }
        print!("\nInner free vars:\n");
        for inner_free_var in &inner_free_vars_list {
            println!("{}", inner_free_var.for_formatting(storage_ref.global_storage()));
        }

        println!();
    }
}
