//! Functionality related to variable substitution inside terms/types.
use super::{AccessToOps, AccessToOpsMut};
use crate::storage::{
    primitives::{
        Arg, ArgsId, ConstructedTerm, FnTy, Level0Term, Level1Term, Level2Term, Level3Term, Param,
        ParamsId, ScopeId, Sub, SubVar, Term, TermId, TupleTy, TyFn, TyFnCall, TyFnCase, TyFnTy,
    },
    AccessToStorage, AccessToStorageMut, StorageRefMut,
};

/// Can perform substitutions (see [Sub]) on terms.
pub struct Substituter<'tc> {
    storage: StorageRefMut<'tc>,
}

impl<'tc> AccessToStorage for Substituter<'tc> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'tc> AccessToStorageMut for Substituter<'tc> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'tc> Substituter<'tc> {
    pub fn new(storage: StorageRefMut<'tc>) -> Self {
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
    pub fn apply_sub_to_level3_term(
        &mut self,
        _: &Sub,
        term: Level3Term,
        original_term: TermId,
    ) -> TermId {
        match term {
            Level3Term::TrtKind => original_term,
        }
    }

    /// Apply the given substitution to the given [Level2Term], producing a new
    /// [Level2Term] with the substituted variables.
    pub fn apply_sub_to_level2_term(
        &mut self,
        _sub: &Sub,
        term: Level2Term,
        original_term: TermId,
    ) -> TermId {
        match term {
            Level2Term::Trt(_) | Level2Term::AnyTy => original_term,
        }
    }

    /// Apply the given substitution to the given [Level1Term], producing a new
    /// [Level1Term] with the substituted variables.
    pub fn apply_sub_to_level1_term(
        &mut self,
        sub: &Sub,
        term: Level1Term,
        original_term: TermId,
    ) -> TermId {
        match term {
            Level1Term::ModDef(_) | Level1Term::NominalDef(_) => original_term,
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
            Level0Term::Constructed(ConstructedTerm { subject, members }) => {
                let subbed_subject = self.apply_sub_to_term(sub, subject);
                let subbed_args = self.apply_sub_to_args(sub, members);

                self.builder().create_constructed_term(subbed_subject, subbed_args)
            }
            Level0Term::Lit(_) | Level0Term::EnumVariant(_) => original_term,
        }
    }

    /// Apply the given substitution to the given scope, creating a new scope
    /// with the applied substitution.
    ///
    /// This is only ever applied for [ScopeKind::SetBound].
    pub fn apply_sub_to_scope(&mut self, sub: &Sub, scope_id: ScopeId) -> ScopeId {
        let reader = self.reader();
        let old_scope = reader.get_scope(scope_id).clone();
        let mut new_members = vec![];
        for old_member in old_scope.iter() {
            let new_value = old_member.value().map(|value| self.apply_sub_to_term(sub, value));
            let new_ty = self.apply_sub_to_term(sub, old_member.ty());
            new_members.push(old_member.with_ty_and_value(new_ty, new_value));
        }
        self.builder().create_scope(old_scope.kind, new_members)
    }

    /// Apply the given substitution to the given [SubVar], producing a new
    /// term with the substituted result.
    pub fn apply_sub_to_subject(&mut self, sub: &Sub, subject: SubVar) -> TermId {
        match sub.get_sub_for(subject) {
            Some(subbed_term_id) => subbed_term_id,
            None => self.builder().create_term(subject.into()),
        }
    }

    /// Apply the given substitution to the term indexed by the given [TermId],
    /// producing a new term with the substituted variables.
    pub fn apply_sub_to_term(&mut self, sub: &Sub, term_id: TermId) -> TermId {
        // Short circuit: no vars in the sub and in the term match:
        let vars_in_term = self.discoverer().get_free_sub_vars_in_term(term_id);
        if !sub.domain().any(|var| vars_in_term.contains(&var)) {
            return term_id;
        }

        let term = self.reader().get_term(term_id).clone();

        let new_term = match term {
            // Leaves:
            Term::ScopeVar(_) | Term::Var(_) | Term::BoundVar(_) | Term::Root => term_id,
            Term::Unresolved(unresolved) => self.apply_sub_to_subject(sub, unresolved.into()),

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
            Term::TyFn(ty_fn) => {
                // Apply the substitution to the general parameters, return type, and each case.
                let general_params = self.apply_sub_to_params(sub, ty_fn.general_params);
                let general_return_ty = self.apply_sub_to_term(sub, ty_fn.general_return_ty);

                let cases = ty_fn
                    .cases
                    .into_iter()
                    .map(|case| TyFnCase {
                        params: self.apply_sub_to_params(sub, case.params),
                        return_ty: self.apply_sub_to_term(sub, case.return_ty),
                        return_value: self.apply_sub_to_term(sub, case.return_value),
                    })
                    .collect::<Vec<_>>();

                self.builder().create_term(Term::TyFn(TyFn {
                    name: ty_fn.name,
                    general_params,
                    general_return_ty,
                    cases,
                }))
            }
            Term::TyFnTy(ty_fn_ty) => {
                // Apply the substitution to the parameters and return type.
                let params = self.apply_sub_to_params(sub, ty_fn_ty.params);
                let return_ty = self.apply_sub_to_term(sub, ty_fn_ty.return_ty);
                self.builder().create_term(Term::TyFnTy(TyFnTy { params, return_ty }))
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
            Term::SetBound(set_bound) => {
                // Apply to the scope and the term:
                let scope = self.apply_sub_to_scope(sub, set_bound.scope);
                let term = self.apply_sub_to_term(sub, set_bound.term);
                self.builder().create_set_bound_term(term, scope)
            }
            Term::TyOf(term) => {
                // Apply sub to inner:
                let subbed_term = self.apply_sub_to_term(sub, term);
                self.builder().create_ty_of_term(subbed_term)
            }
            // Definite-level terms:
            Term::Level3(term) => self.apply_sub_to_level3_term(sub, term, term_id),
            Term::Level2(term) => self.apply_sub_to_level2_term(sub, term, term_id),
            Term::Level1(term) => self.apply_sub_to_level1_term(sub, term, term_id),
            Term::Level0(term) => self.apply_sub_to_level0_term(sub, term, term_id),
        };

        self.location_store_mut().copy_location(term_id, new_term);
        new_term
    }
}
