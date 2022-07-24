//! Functionality related to variable substitution inside terms/types.
use super::{AccessToOps, AccessToOpsMut};
use crate::storage::{
    primitives::{
        Arg, ArgsId, ConstructedTerm, FnTy, Level0Term, Level1Term, Level2Term, Level3Term, Param,
        ParamsId, Sub, SubVar, Term, TermId, TupleTy, TyFnCall,
    },
    AccessToStorage, AccessToStorageMut, StorageRefMut,
};

/// Can perform substitutions (see [Sub]) on terms.
pub struct Substituter<'gs, 'ls, 'cd, 's> {
    storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for Substituter<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd, 's> AccessToStorageMut for Substituter<'gs, 'ls, 'cd, 's> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 's> Substituter<'gs, 'ls, 'cd, 's> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd, 's>) -> Self {
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

        self.builder().create_args(new_args, args.origin())
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

        self.builder().create_params(new_params, params.origin())
    }

    /// Apply the given substitution to the given [FnTy], producing a new
    /// [FnTy] with the substituted variables.
    pub fn apply_sub_to_fn_ty(&mut self, sub: &Sub, fn_ty: FnTy) -> FnTy {
        // Apply to parameters and return type
        let subbed_params = self.apply_sub_to_params(sub, fn_ty.params);
        let subbed_return_ty = self.apply_sub_to_term(sub, fn_ty.return_ty);
        FnTy { params: subbed_params, return_ty: subbed_return_ty }
    }

    /// Apply the given substitution to the given [ConstructedTerm], producing a
    /// new [ConstructedTerm] with the substituted variables.
    pub fn apply_sub_to_constructed_ty(
        &mut self,
        sub: &Sub,
        term: ConstructedTerm,
    ) -> ConstructedTerm {
        let members = self.apply_sub_to_args(sub, term.members);
        let subject = self.apply_sub_to_term(sub, term.subject);

        ConstructedTerm { subject, members }
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
    pub fn apply_sub_to_level2_term(&mut self, _sub: &Sub, term: Level2Term) -> TermId {
        match term {
            Level2Term::Trt(_trt_def_id) => {
                // Here we add the substitution to the term using only vars in the trait
                // definition.
                // let reader = self.reader();
                // let trt_def_vars = &reader.get_trt_def(trt_def_id).bound_vars;
                // let selected_sub = sub.select(trt_def_vars);
                // let builder = self.builder();
                // builder.create_app_sub_term(selected_sub,
                // builder.create_term(Term::Level2(term)))
                todo!()
            }
            Level2Term::AnyTy => (self.builder().create_term(Term::Level2(Level2Term::AnyTy))),
        }
    }

    /// Apply the given substitution to the given [Level1Term], producing a new
    /// [Level1Term] with the substituted variables.
    pub fn apply_sub_to_level1_term(&mut self, sub: &Sub, term: Level1Term) -> TermId {
        match term {
            Level1Term::ModDef(_mod_def_id) => {
                // Here we add the substitution to the term using only vars in the mod
                // definition.
                // let reader = self.reader();
                // let mod_def_vars = &reader.get_mod_def(mod_def_id).bound_vars;
                // let selected_sub = sub.select(mod_def_vars);
                // let builder = self.builder();
                // builder.create_app_sub_term(selected_sub,
                // builder.create_term(Term::Level1(term)))
                todo!()
            }
            Level1Term::NominalDef(_nominal_def_id) => {
                // Here we add the substitution to the term using only vars in the nominal
                // definition.
                // let reader = self.reader();
                // let nominal_def_vars = reader.get_nominal_def(nominal_def_id).bound_vars();
                // let selected_sub = sub.select(nominal_def_vars);
                // let builder = self.builder();
                // builder.create_app_sub_term(selected_sub,
                // builder.create_term(Term::Level1(term)))
                todo!()
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
                let subbed_fn_ty = self.apply_sub_to_fn_ty(sub, fn_ty);
                self.builder().create_term(Term::Level1(Level1Term::Fn(subbed_fn_ty)))
            }
        }
    }

    /// Apply the given substitution to the given [Level0Term], producing a new
    /// [Level0Term] with the substituted variables.
    pub fn apply_sub_to_level0_term(
        &mut self,
        sub: &Sub,
        term: Level0Term,
        original_term: TermId,
    ) -> TermId {
        match term {
            Level0Term::Rt(ty_term_id) => {
                // Apply to the type of the runtime value
                let subbed_ty_term_id = self.apply_sub_to_term(sub, ty_term_id);
                self.builder().create_rt_term(subbed_ty_term_id)
            }
            Level0Term::EnumVariant(_enum_variant) => {
                // Here we add the substitution to the term using only vars in the enum
                // definition.
                // let reader = self.reader();
                // let enum_def_vars =
                // reader.get_nominal_def(enum_variant.enum_def_id).bound_vars();
                // let selected_sub = sub.select(enum_def_vars);
                // let builder = self.builder();
                // builder.create_app_sub_term(
                //     selected_sub,
                //     builder.create_term(Term::Level0(Level0Term::EnumVariant(enum_variant))),
                // )
                todo!()
            }
            Level0Term::FnLit(fn_lit) => {
                // Apply to the function type and return value
                let subbed_fn_ty = self.apply_sub_to_term(sub, fn_lit.fn_ty);
                let subbed_return_value = self.apply_sub_to_term(sub, fn_lit.return_value);
                self.builder().create_fn_lit_term(subbed_fn_ty, subbed_return_value)
            }
            Level0Term::FnCall(fn_call) => {
                // Apply to subject and args
                let subbed_subject = self.apply_sub_to_term(sub, fn_call.subject);
                let subbed_args = self.apply_sub_to_args(sub, fn_call.args);
                self.builder().create_fn_call_term(subbed_subject, subbed_args)
            }
            Level0Term::Tuple(tuple_lit) => {
                let subbed_args = self.apply_sub_to_args(sub, tuple_lit.members);
                self.builder().create_tuple_lit_term(subbed_args)
            }
            Level0Term::Lit(_) => original_term,
            Level0Term::Constructed(ConstructedTerm { subject, members }) => {
                let subbed_subject = self.apply_sub_to_term(sub, subject);
                let subbed_args = self.apply_sub_to_args(sub, members);

                self.builder().create_constructed_term(subbed_subject, subbed_args)
            }
        }
    }

    /// Apply the given substitution to the given [SubSubject], producing a new
    /// term with the substituted result.
    pub fn apply_sub_to_subject(&mut self, sub: &Sub, subject: SubVar) -> TermId {
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
            Term::Var(_var) => term_id,
            Term::BoundVar(_var) => term_id,
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
            Term::Union(terms) => {
                // Apply the substitution to each element of the union.
                let terms = terms
                    .into_iter()
                    .map(|term| self.apply_sub_to_term(sub, term))
                    .collect::<Vec<_>>();
                self.builder().create_term(Term::Union(terms))
            }
            Term::TyFn(_ty_fn) => {
                // Apply the substitution to the general parameters, return type, and each case.
                //
                // However, we first have to remove all the shadowed variables from the
                // substitution: If we have T -> str, and <T> => List<T>, we
                // don't wanna get <T> => List<str> because T is bound in the
                // term, not free.
                // let params = self.params_store().get(ty_fn.general_params).clone();

                // let shadowed_sub = sub.filter(params);
                // let subbed_general_params =
                //     self.apply_sub_to_params(&shadowed_sub, ty_fn.general_params);
                // let subbed_general_return_ty =
                //     self.apply_sub_to_term(&shadowed_sub, ty_fn.general_return_ty);

                // let subbed_cases = ty_fn
                //     .cases
                //     .into_iter()
                //     .map(|case| TyFnCase {
                //         params: self.apply_sub_to_params(&shadowed_sub, case.params),
                //         return_ty: self.apply_sub_to_term(&shadowed_sub, case.return_ty),
                //         return_value: self.apply_sub_to_term(&shadowed_sub,
                // case.return_value),     })
                //     .collect::<Vec<_>>();
                // self.builder().create_term(Term::TyFn(TyFn {
                //     name: ty_fn.name,
                //     general_params: subbed_general_params,
                //     general_return_ty: subbed_general_return_ty,
                //     cases: subbed_cases,
                // }))
                todo!()
            }
            Term::TyFnTy(ty_fn_ty) => {
                // Apply the substitution to the parameters and return type.
                // Same rule applies about binding as above.
                let _params = self.params_store().get(ty_fn_ty.params).clone();

                // let shadowed_sub = sub.filter(params);
                // let subbed_params = self.apply_sub_to_params(&shadowed_sub, ty_fn_ty.params);
                // let subbed_return_ty = self.apply_sub_to_term(&shadowed_sub,
                // ty_fn_ty.return_ty); self.builder().
                // create_term(Term::TyFnTy(TyFnTy {     params: subbed_params,
                //     return_ty: subbed_return_ty,
                // }))
                todo!()
            }
            Term::TyFnCall(app_ty_fn) => {
                // Apply the substitution to the subject and arguments.
                let subbed_subject = self.apply_sub_to_term(sub, app_ty_fn.subject);
                let subbed_args = self.apply_sub_to_args(sub, app_ty_fn.args);
                self.builder().create_term(Term::TyFnCall(TyFnCall {
                    subject: subbed_subject,
                    args: subbed_args,
                }))
            }
            Term::SetBound(_app_sub) => {
                // @@Correctness: do we not want to unify substitutions here?
                //
                // Here, we have to substitute all X in * -> X pairs of the substitution, as
                // well as the subject term itself.
                // let subbed_sub = app_sub
                //     .sub
                //     .pairs()
                //     .map(|(from, to)| (from, self.apply_sub_to_term(sub, to)))
                //     .collect::<HashMap<_, _>>();
                // let subbed_term = self.apply_sub_to_term(sub, app_sub.term);
                // self.builder().create_term(Term::SetBound(AppSub {
                //     sub: Sub::from_map(subbed_sub),
                //     term: subbed_term,
                // }))
                todo!()
            }
            Term::TyOf(term) => {
                // Apply sub to inner:
                let subbed_term = self.apply_sub_to_term(sub, term);
                self.builder().create_ty_of_term(subbed_term)
            }
            // Definite-level terms:
            Term::Level3(term) => self.apply_sub_to_level3_term(sub, term),
            Term::Level2(term) => self.apply_sub_to_level2_term(sub, term),
            Term::Level1(term) => self.apply_sub_to_level1_term(sub, term),
            Term::Level0(term) => self.apply_sub_to_level0_term(sub, term, term_id),
            Term::ScopeVar(_) => todo!(),
        };

        self.location_store_mut().copy_location(term_id, new_term);
        new_term
    }
}

#[cfg(test)]
mod tests {
    use hash_ast::ast::ParamOrigin;
    use hash_source::SourceMap;

    use crate::{
        fmt::PrepareForFormatting,
        ops::AccessToOpsMut,
        storage::{
            core::CoreDefs,
            primitives::{ModDefOrigin, ScopeKind},
            AccessToStorage, GlobalStorage, LocalStorage, StorageRefMut,
        },
    };

    fn _get_storages() -> (GlobalStorage, LocalStorage, CoreDefs, SourceMap) {
        let mut global_storage = GlobalStorage::new();
        let local_storage = LocalStorage::new(&mut global_storage);
        let core_defs = CoreDefs::new(&mut global_storage);
        let source_map = SourceMap::new();

        (global_storage, local_storage, core_defs, source_map)
    }

    // #[test]
    fn _test_substitutions() {
        let (mut global_storage, mut local_storage, core_defs, source_map) = _get_storages();
        let mut storage_ref = StorageRefMut {
            global_storage: &mut global_storage,
            local_storage: &mut local_storage,
            core_defs: &core_defs,
            source_map: &source_map,
        };

        let builder = storage_ref.builder();

        // Visual testing for now, until term unification is implemented and we can
        // actually write proper tests here:
        let hash_impl = builder.create_nameless_mod_def(
            ModDefOrigin::TrtImpl(builder.create_trt_term(core_defs.hash_trt)),
            builder.create_scope(ScopeKind::Constant, []),
        );

        let inner = builder.create_nameless_ty_fn_term(
            builder.create_params(
                [builder.create_param("T", builder.create_any_ty_term())],
                ParamOrigin::TyFn,
            ),
            builder.create_any_ty_term(),
            builder.create_app_ty_fn_term(
                core_defs.set_ty_fn,
                builder.create_args(
                    [
                        builder.create_arg("T", builder.create_var_term("T")),
                        builder.create_arg("X", builder.create_mod_def_term(hash_impl)),
                    ],
                    ParamOrigin::TyFn,
                ),
            ),
        );
        let target = builder.create_ty_fn_ty_term(
            builder.create_params(
                [builder.create_param("U", builder.create_any_ty_term())],
                ParamOrigin::TyFn,
            ),
            builder.create_fn_ty_term(
                builder.create_params(
                    [
                        builder.create_param("foo", builder.create_unresolved_term()),
                        builder.create_param(
                            "bar",
                            builder.create_app_ty_fn_term(
                                core_defs.list_ty_fn,
                                builder.create_args(
                                    [builder.create_arg("T", inner)],
                                    ParamOrigin::TyFn,
                                ),
                            ),
                        ),
                    ],
                    ParamOrigin::Fn,
                ),
                builder.create_var_term("T"),
            ),
        );

        println!("\n{}", target.for_formatting(storage_ref.global_storage()));

        let _builder = storage_ref.builder();
        todo!()
        // let sub = Sub::from_pairs([(
        //     builder.create_var("T"),
        //     builder.create_var("T"),
        //     builder.create_app_ty_fn_term(
        //         core_defs.map_ty_fn,
        //         builder.create_args(
        //             [
        //                 builder.create_arg("K",
        // builder.create_nominal_def_term(core_defs.str_ty)),
        //                 builder.create_arg("V",
        // builder.create_nominal_def_term(core_defs.u64_ty)),
        //             ],
        //             ParamOrigin::TyFn,
        //         ),
        //     ),
        // )]);

        // let mut substituter = Substituter::new(storage_ref.storages_mut());
        // let subbed_target = substituter.apply_sub_to_term(&sub, target);

        // let target_free_vars = substituter.get_free_vars_in_term(target);
        // let inner_free_vars = substituter.get_free_vars_in_term(inner);

        // let target_free_vars_list: Vec<_> = target_free_vars
        //     .into_iter()
        //     .map(|x| storage_ref.builder().create_term(x.into()))
        //     .collect();

        // let inner_free_vars_list: Vec<_> = inner_free_vars
        //     .into_iter()
        //     .map(|x| storage_ref.builder().create_term(x.into()))
        //     .collect();

        // println!("{}",
        // subbed_target.for_formatting(storage_ref.global_storage()));

        // print!("\nTarget free vars:\n");
        // for target_free_var in &target_free_vars_list {
        //     println!("{}",
        // target_free_var.for_formatting(storage_ref.global_storage()));
        // }
        // print!("\nInner free vars:\n");
        // for inner_free_var in &inner_free_vars_list {
        //     println!("{}",
        // inner_free_var.for_formatting(storage_ref.global_storage()));
        // }
    }
}
