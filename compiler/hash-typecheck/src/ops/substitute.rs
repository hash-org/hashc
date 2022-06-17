//! Functionality related to variable substitution inside terms/types.
use crate::storage::{
    primitives::{
        AppSub, AppTyFn, Arg, Args, FnTy, Level0Term, Level1Term, Level2Term, Level3Term, Param,
        ParamList, Params, Sub, SubSubject, Term, TermId, TupleTy, TyFn, TyFnCase, TyFnTy,
    },
    AccessToStorage, AccessToStorageMut, StorageRefMut,
};
use std::collections::{HashMap, HashSet};

/// Can perform substitutions (see [Sub]) on terms.
pub struct Substitutor<'gs, 'ls, 'cd> {
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for Substitutor<'gs, 'ls, 'cd> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> AccessToStorageMut for Substitutor<'gs, 'ls, 'cd> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd> Substitutor<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    /// Apply the given substitution to the given arguments, producing a new set of arguments
    /// with the substituted variables.
    pub fn apply_sub_to_args(&mut self, sub: &Sub, args: &Args) -> Args {
        let new_args = args
            .positional()
            .iter()
            .map(|arg| Arg {
                name: arg.name,
                value: self.apply_sub_to_term(sub, arg.value),
            })
            .collect::<Vec<_>>();
        ParamList::new(new_args)
    }

    /// Apply the given substitution to the given parameters, producing a new set of parameters
    /// with the substituted variables.
    pub fn apply_sub_to_params(&mut self, sub: &Sub, params: &Params) -> Params {
        let new_params = params
            .positional()
            .iter()
            .map(|param| Param {
                name: param.name,
                ty: self.apply_sub_to_term(sub, param.ty),
                default_value: param
                    .default_value
                    .map(|value| self.apply_sub_to_term(sub, value)),
            })
            .collect::<Vec<_>>();
        ParamList::new(new_params)
    }

    /// Apply the given substitution to the given [Level3Term], producing a new [Level3Term] with
    /// the substituted variables.
    pub fn apply_sub_to_level3_term(&mut self, _: &Sub, term: Level3Term) -> TermId {
        match term {
            Level3Term::TrtKind => self
                .builder()
                .create_term(Term::Level3(Level3Term::TrtKind)),
        }
    }

    /// Apply the given substitution to the given [Level2Term], producing a new [Level2Term] with
    /// the substituted variables.
    pub fn apply_sub_to_level2_term(&mut self, sub: &Sub, term: Level2Term) -> TermId {
        match term {
            Level2Term::Trt(trt_def_id) => {
                // Here we add the substitution to the term using only vars in the trat definition.
                let reader = self.reader();
                let trt_def_vars = &reader.get_trt_def(trt_def_id).bound_vars;
                let selected_sub = sub.select(trt_def_vars);
                let builder = self.builder();
                builder.create_app_sub_term(selected_sub, builder.create_term(Term::Level2(term)))
            }
            Level2Term::AnyTy => (self.builder().create_term(Term::Level2(Level2Term::AnyTy))),
        }
    }

    /// Apply the given substitution to the given [Level1Term], producing a new [Level1Term] with
    /// the substituted variables.
    pub fn apply_sub_to_level1_term(&mut self, sub: &Sub, term: Level1Term) -> TermId {
        match term {
            Level1Term::ModDef(mod_def_id) => {
                // Here we add the substitution to the term using only vars in the mod definition.
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
                let subbed_members = self.apply_sub_to_params(sub, &tuple_ty.members);
                self.builder()
                    .create_term(Term::Level1(Level1Term::Tuple(TupleTy {
                        members: subbed_members,
                    })))
            }
            Level1Term::Fn(fn_ty) => {
                // Apply to parameters and return type
                let subbed_params = self.apply_sub_to_params(sub, &fn_ty.params);
                let subbed_return_ty = self.apply_sub_to_term(sub, fn_ty.return_ty);
                self.builder()
                    .create_term(Term::Level1(Level1Term::Fn(FnTy {
                        params: subbed_params,
                        return_ty: subbed_return_ty,
                    })))
            }
        }
    }

    /// Apply the given substitution to the given [Level0Term], producing a new [Level0Term] with
    /// the substituted variables.
    pub fn apply_sub_to_level0_term(&mut self, sub: &Sub, term: Level0Term) -> TermId {
        match term {
            Level0Term::Rt(ty_term_id) => {
                // Apply to the type of the runtime value
                let subbed_ty_term_id = self.apply_sub_to_term(sub, ty_term_id);
                self.builder().create_rt_term(subbed_ty_term_id)
            }
            Level0Term::EnumVariant(enum_variant) => {
                // Here we add the substitution to the term using only vars in the enum definition.
                let reader = self.reader();
                let enum_def_vars = reader
                    .get_nominal_def(enum_variant.enum_def_id)
                    .bound_vars();
                let selected_sub = sub.select(enum_def_vars);
                let builder = self.builder();
                builder.create_app_sub_term(
                    selected_sub,
                    builder.create_term(Term::Level0(Level0Term::EnumVariant(enum_variant))),
                )
            }
        }
    }

    /// Apply the given substitution to the given [SubSubject], producing a new term with the
    /// substituted result.
    pub fn apply_sub_to_subject(&mut self, sub: &Sub, subject: SubSubject) -> TermId {
        match sub.get_sub_for(subject) {
            Some(subbed_term_id) => subbed_term_id,
            None => self.builder().create_term(subject.into()),
        }
    }

    /// Apply the given substitution to the term indexed by the given [TermId], producing a new
    /// term with the substituted variables.
    ///
    /// Sometimes, this will actually create a [Term::AppSub] somewhere inside the term tree, and
    /// those are the leaf nodes of the substitution application. This will happen with `ModDef`,
    /// `TrtDef`, `NominalDef`, and `EnumVariant`. This is so that when `Access` is resolved for
    /// those types, the substitution is carried forward into the member term.
    pub fn apply_sub_to_term(&mut self, sub: &Sub, term_id: TermId) -> TermId {
        // @@Performance: here we copy a lot, maybe there is a way to avoid all this copying by
        // first checking that the variables to be substituted actually exist in the term.

        let term = self.reader().get_term(term_id).clone();
        match term {
            // Leaves:
            Term::Var(var) => self.apply_sub_to_subject(sub, var.into()),
            Term::Unresolved(unresolved) => self.apply_sub_to_subject(sub, unresolved.into()),

            // Recursive cases:
            Term::Access(access) => {
                // Just apply the substitution to the subject:
                let subbed_subject_id = self.apply_sub_to_term(sub, access.subject_id);
                self.builder().create_access(subbed_subject_id, access.name)
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
                // However, we first have to remove all the shadowed variables from the substitution:
                // If we have T -> str, and <T> => List<T>, we don't wanna get <T> => List<str>
                // because T is bound in the term, not free.
                let shadowed_sub = sub.filter(&ty_fn.general_params);
                let subbed_general_params =
                    self.apply_sub_to_params(&shadowed_sub, &ty_fn.general_params);
                let subbed_general_return_ty =
                    self.apply_sub_to_term(&shadowed_sub, ty_fn.general_return_ty);
                let subbed_cases = ty_fn
                    .cases
                    .into_iter()
                    .map(|case| TyFnCase {
                        params: self.apply_sub_to_params(&shadowed_sub, &case.params),
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
                let shadowed_sub = sub.filter(&ty_fn_ty.params);
                let subbed_params = self.apply_sub_to_params(&shadowed_sub, &ty_fn_ty.params);
                let subbed_return_ty = self.apply_sub_to_term(&shadowed_sub, ty_fn_ty.return_ty);
                self.builder().create_term(Term::TyFnTy(TyFnTy {
                    params: subbed_params,
                    return_ty: subbed_return_ty,
                }))
            }
            Term::AppTyFn(app_ty_fn) => {
                // Apply the substitution to the subject and arguments.
                let subbed_subject = self.apply_sub_to_term(sub, app_ty_fn.subject);
                let subbed_args = self.apply_sub_to_args(sub, &app_ty_fn.args);
                self.builder().create_term(Term::AppTyFn(AppTyFn {
                    subject: subbed_subject,
                    args: subbed_args,
                }))
            }
            Term::AppSub(app_sub) => {
                // Here, we have to substitute all X in * -> X pairs of the substitution, as well
                // as the subject term itself.
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
        }
    }

    /// Get the set of free variables that exist in the given term.
    ///
    /// Free variables are either `Var` or `Unresolved`, and this function collects both.
    pub fn get_free_vars_in_term(&self, _term: TermId) -> HashSet<SubSubject> {
        // @@Todo
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fmt::PrepareForFormatting,
        storage::{
            core::CoreDefs, primitives::Sub, AccessToStorage, AccessToStorageMut, GlobalStorage,
            LocalStorage, StorageRefMut,
        },
    };
    use hash_source::{InteractiveId, SourceId};
    use slotmap::Key;

    use super::Substitutor;

    #[test]
    fn test_substitutions() {
        let mut global_storage = GlobalStorage::new();
        let mut local_storage = LocalStorage::new(
            SourceId::Interactive(InteractiveId::null()),
            &mut global_storage,
        );
        let core_defs = CoreDefs::new(&mut global_storage);
        let mut storage_ref = StorageRefMut {
            core_defs: &core_defs,
            global_storage: &mut global_storage,
            local_storage: &mut local_storage,
        };

        let builder = storage_ref.builder();

        // Visual testing for now, until term unification is implemented and we can actually write proper tests here:

        let inner = builder.create_nameless_ty_fn_term(
            [builder.create_param("T", builder.create_any_ty_term())],
            builder.create_any_ty_term(),
            builder.create_app_ty_fn_term(
                core_defs.set_ty_fn,
                [builder.create_arg("T", builder.create_var_term("T"))],
            ),
        );
        let target = builder.create_fn_ty_term(
            [
                builder.create_param("foo", builder.create_nominal_def_term(core_defs.f32_ty)),
                builder.create_param(
                    "bar",
                    builder.create_app_ty_fn_term(
                        core_defs.list_ty_fn,
                        [builder.create_arg("T", inner)],
                    ),
                ),
            ],
            builder.create_var_term("T"),
        );

        println!();

        println!("{}", target.for_formatting(storage_ref.global_storage()));

        let builder = storage_ref.builder();
        let sub = Sub::from_pairs([(
            builder.create_var("T"),
            builder.create_app_ty_fn_term(
                core_defs.map_ty_fn,
                [
                    builder.create_arg("K", builder.create_nominal_def_term(core_defs.str_ty)),
                    builder.create_arg("V", builder.create_nominal_def_term(core_defs.u64_ty)),
                ],
            ),
        )]);

        let mut substitutor = Substitutor::new(storage_ref.storages_mut());
        let subbed_target = substitutor.apply_sub_to_term(&sub, target);

        println!(
            "{}",
            subbed_target.for_formatting(storage_ref.global_storage())
        );

        println!();
    }
}
