//! Operations for unifying types and terms.

use std::cell::Cell;

use derive_more::Deref;
use hash_tir::{
    args::{ArgData, ArgsId, PatArgData, PatArgsId, PatOrCapture},
    data::{DataDefCtors, DataTy},
    environment::context::{ParamOrigin, ScopeKind},
    fns::{FnBody, FnTy},
    holes::Hole,
    lits::Lit,
    locations::LocationTarget,
    params::{ParamData, ParamsId},
    pats::{Pat, PatId, PatListId},
    refs::RefTy,
    sub::Sub,
    symbols::Symbol,
    terms::{Term, TermId},
    tuples::TupleTy,
    tys::{Ty, TyId},
    utils::{common::CommonUtils, traversing::Atom, AccessToUtils},
};
use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey};

use crate::{
    errors::{TcError, TcResult},
    inference::Inference,
    params::ParamError,
    AccessToTypechecking,
};

/// Represents a unification result.
#[derive(Debug, Clone)]
pub struct Uni<T> {
    pub result: T,
    pub sub: Sub,
}

impl<T> Uni<T> {
    /// Create a unification result that is successful and has no substitution.
    pub fn ok(result: T) -> TcResult<Self> {
        Ok(Uni { sub: Sub::identity(), result })
    }

    /// Create a unification result that is successful and has the given
    /// substitution.
    pub fn ok_with(sub: Sub, result: T) -> TcResult<Self> {
        Ok(Uni { sub, result })
    }

    /// Create a unification result that is blocked.
    pub fn blocked(loc: impl Into<LocationTarget>) -> TcResult<Self> {
        Err(TcError::Blocked(loc.into()))
    }

    /// Create a unification result that is an error of mismatching terms.
    ///
    /// Invariant: `src_id` and `target_id` must be of the same atom kind.
    pub fn mismatch_atoms(src_id: impl Into<Atom>, target_id: impl Into<Atom>) -> TcResult<Self> {
        match (src_id.into(), target_id.into()) {
            (Atom::Term(a), Atom::Term(b)) => Err(TcError::UndecidableEquality { a, b }),
            (Atom::Ty(a), Atom::Ty(b)) => {
                Err(TcError::MismatchingTypes { expected: b, actual: a, inferred_from: None })
            }
            (Atom::FnDef(a), Atom::FnDef(b)) => Err(TcError::MismatchingFns { a, b }),
            (Atom::Pat(a), Atom::Pat(b)) => Err(TcError::MismatchingPats { a, b }),
            _ => unreachable!(),
        }
    }

    pub fn map_result<U>(self, f: impl FnOnce(T) -> U) -> Uni<U> {
        Uni { result: f(self.result), sub: self.sub }
    }

    pub fn map_into<U>(self) -> Uni<U>
    where
        T: Into<U>,
    {
        Uni { result: self.result.into(), sub: self.sub }
    }
}

impl Uni<TyId> {
    /// Create a unification result that is an error of mismatching types if
    /// `cond` is false, and successful otherwise.
    pub fn ok_iff_types_match(cond: bool, src_id: TyId, target_id: TyId) -> TcResult<Uni<TyId>> {
        if cond {
            Uni::ok(target_id)
        } else {
            Uni::mismatch_atoms(src_id, target_id)
        }
    }
}

impl Uni<TermId> {
    /// Create a unification result that is an error of mismatching terms if
    /// `cond` is false, and successful otherwise.
    pub fn ok_iff_atoms_match<I: Into<Atom>>(
        cond: bool,
        src_id: I,
        target_id: I,
    ) -> TcResult<Uni<I>> {
        if cond {
            Uni::ok(target_id)
        } else {
            Uni::mismatch_atoms(src_id, target_id)
        }
    }
}

#[derive(Deref)]
pub struct UnificationOps<'a, T: AccessToTypechecking> {
    #[deref]
    env: &'a T,
    add_to_ctx: Cell<bool>,
}

impl<'tc, T: AccessToTypechecking> UnificationOps<'tc, T> {
    pub fn new(env: &'tc T) -> Self {
        Self { env, add_to_ctx: Cell::new(true) }
    }

    pub fn with_no_ctx(&self) -> &Self {
        self.add_to_ctx.set(false);
        self
    }

    pub fn unify_atoms(&self, src: Atom, target: Atom) -> TcResult<Uni<Atom>> {
        match (src, target) {
            (Atom::Ty(src_id), Atom::Ty(target_id)) => {
                Ok(self.unify_tys(src_id, target_id)?.map_into())
            }
            (Atom::Term(src_id), Atom::Term(target_id)) => {
                Ok(self.unify_terms(src_id, target_id)?.map_into())
            }
            _ => panic!("unify_atoms: mismatching atoms"),
        }
    }

    pub fn add_unification_from_sub(&self, sub: &Sub) {
        if self.add_to_ctx.get() {
            self.context_utils().add_sub_to_scope(sub);
        }
    }

    pub fn add_unification(&self, src: Symbol, target: impl Into<Atom>) -> Sub {
        let sub = Sub::from_pairs([(src, self.norm_ops().to_term(target.into()))]);
        self.add_unification_from_sub(&sub);
        sub
    }

    /// Unified two function types.
    pub fn unify_fn_tys(
        &self,
        f1: FnTy,
        f2: FnTy,
        src_id: impl Into<Atom>,
        target_id: impl Into<Atom>,
    ) -> TcResult<Uni<FnTy>> {
        if !self.fn_modalities_match(f1, f2) {
            Uni::mismatch_atoms(src_id, target_id)
        } else {
            // Unify parameters and apply to return types
            let (return_ty, shadowed_sub) =
                self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
                    let _ = self.unify_params(f2.params, f1.params, ParamOrigin::FnTy(f1))?;
                    let Uni { result: return_ty, sub: return_ty_sub } =
                        self.unify_tys(f1.return_ty, f2.return_ty)?;
                    let scope_sub = self.sub_ops().create_sub_from_current_scope();
                    let shadowed_sub = self
                        .sub_ops()
                        .hide_param_binds(f1.params.iter().chain(f2.params.iter()), &scope_sub);

                    Ok((return_ty, shadowed_sub))
                })?;

            // Add to context
            self.add_unification_from_sub(&shadowed_sub);
            Ok(Uni { result: FnTy { return_ty, params: f1.params, ..f1 }, sub: shadowed_sub })
        }
    }

    /// Unify two types.
    pub fn unify_tys(&self, src_id: TyId, target_id: TyId) -> TcResult<Uni<TyId>> {
        let norm_ops = self.norm_ops();

        let src_id = norm_ops.to_ty(norm_ops.normalise(src_id.into())?);
        let target_id = norm_ops.to_ty(norm_ops.normalise(target_id.into())?);

        let src = self.get_ty(src_id);
        let target = self.get_ty(target_id);

        let result = match (src, target) {
            (Ty::Hole(a), Ty::Hole(b)) => {
                if a == b {
                    // No-op
                    Uni::ok(target_id)
                } else {
                    // We can't unify two holes, so we have to block
                    Uni::blocked(target_id)
                }
            }
            (Ty::Hole(a), _) => {
                let sub = Sub::from_pairs([(a.0, self.new_term(target_id))]);
                if self.add_to_ctx.get() {
                    self.context_utils().add_untyped_assignment(a.0, self.new_term(target_id));
                }
                Uni::ok_with(sub, target_id)
            }
            (_, Ty::Hole(b)) => {
                let sub = Sub::from_pairs([(b.0, self.new_term(src_id))]);
                if self.add_to_ctx.get() {
                    self.context_utils().add_untyped_assignment(b.0, self.new_term(src_id));
                }
                Uni::ok_with(sub, src_id)
            }
            (_, _) if self.is_uninhabitable(src_id)? => Uni::ok(target_id),

            (Ty::Eval(t1), Ty::Eval(t2)) => {
                let uni = self.unify_terms(t1, t2)?;
                // Ensure it is a type
                let result_ty = self.infer_ops().use_term_in_ty_pos(uni.result)?;
                Ok(uni.map_result(|_| result_ty))
            }
            (Ty::Eval(_), _) => Uni::mismatch_atoms(src_id, target_id),
            (_, Ty::Eval(_)) => Uni::mismatch_atoms(src_id, target_id),

            (Ty::Var(a), Ty::Var(b)) => Uni::ok_iff_types_match(a == b, src_id, target_id),
            (Ty::Var(_), _) | (_, Ty::Var(_)) => Uni::mismatch_atoms(src_id, target_id),

            (Ty::Tuple(t1), Ty::Tuple(t2)) => Ok(self
                .unify_params(t1.data, t2.data, ParamOrigin::TupleTy(t1))?
                .map_result(|data| self.new_ty(TupleTy { data }))),
            (Ty::Tuple(_), _) | (_, Ty::Tuple(_)) => Uni::mismatch_atoms(src_id, target_id),

            (Ty::Fn(f1), Ty::Fn(f2)) => {
                if !self.fn_modalities_match(f1, f2) {
                    Uni::mismatch_atoms(src_id, target_id)
                } else {
                    self.context().enter_scope(f2.into(), || {
                        let Uni { sub: param_sub, result: params } =
                            self.unify_params(f1.params, f2.params, ParamOrigin::FnTy(f1))?;

                        let return_ty_1_subbed =
                            self.sub_ops().apply_sub_to_ty(f1.return_ty, &param_sub);
                        let return_ty_2_subbed =
                            self.sub_ops().apply_sub_to_ty(f2.return_ty, &param_sub);

                        let Uni { result: return_ty, sub: return_ty_sub } =
                            self.unify_tys(return_ty_1_subbed, return_ty_2_subbed)?;

                        Ok(Uni {
                            result: self.new_ty(FnTy { return_ty, params, ..f1 }),
                            sub: return_ty_sub.join(&param_sub),
                        })
                    })
                }
            }
            (Ty::Fn(_), _) | (_, Ty::Fn(_)) => Uni::mismatch_atoms(src_id, target_id),

            (Ty::Ref(r1), Ty::Ref(r2)) => {
                if r1.mutable == r2.mutable && r1.kind == r2.kind {
                    let result = self.unify_tys(r1.ty, r2.ty)?;
                    Ok(result.map_result(|ty| self.new_ty(RefTy { ty, ..r1 })))
                } else {
                    Uni::mismatch_atoms(src_id, target_id)
                }
            }
            (Ty::Ref(_), _) | (_, Ty::Ref(_)) => Uni::mismatch_atoms(src_id, target_id),

            (Ty::Data(d1), Ty::Data(d2)) => {
                if d1.data_def == d2.data_def {
                    Ok(self
                        .unify_args(d1.args, d2.args)?
                        .map_result(|args| self.new_ty(DataTy { data_def: d1.data_def, args })))
                } else {
                    Uni::mismatch_atoms(src_id, target_id)
                }
            }
            (Ty::Data(_), _) | (_, Ty::Data(_)) => Uni::mismatch_atoms(src_id, target_id),

            (Ty::Universe(u1), Ty::Universe(u2)) => {
                Uni::ok_iff_types_match(u1.size == u2.size, src_id, target_id)
            }
        }?;

        self.stores().location().copy_location(src_id, result.result);
        Ok(result)
    }

    pub fn lits_are_equal(&self, src: Lit, target: Lit) -> bool {
        match (src, target) {
            (Lit::Int(i1), Lit::Int(i2)) => i1.value() == i2.value(),
            (Lit::Str(s1), Lit::Str(s2)) => s1.value() == s2.value(),
            (Lit::Char(c1), Lit::Char(c2)) => c1.value() == c2.value(),
            (Lit::Float(f1), Lit::Float(f2)) => f1.value() == f2.value(),
            _ => false,
        }
    }

    /// Unify two terms.
    ///
    /// Unless these are types, they must be definitionally (up to beta
    /// reduction) equal.
    pub fn unify_terms(&self, src_id: TermId, target_id: TermId) -> TcResult<Uni<TermId>> {
        if src_id == target_id {
            return Uni::ok(src_id);
        }

        // @@Todo: document and implement remaining cases

        let src_id = self.norm_ops().to_term(self.norm_ops().normalise(src_id.into())?);
        let target_id = self.norm_ops().to_term(self.norm_ops().normalise(target_id.into())?);

        let src = self.get_term(src_id);
        let target = self.get_term(target_id);

        let result = match (self.try_use_term_as_ty(src_id), self.try_use_term_as_ty(target_id)) {
            (Some(src_ty), Some(target_ty)) => {
                let uni = self.unify_tys(src_ty, target_ty)?;
                Ok(uni.map_result(|t| self.new_term(t)))
            }
            _ => match (src, target) {
                (Term::Ty(t1), _) => self.unify_terms(self.use_ty_as_term(t1), target_id),
                (_, Term::Ty(t2)) => self.unify_terms(src_id, self.use_ty_as_term(t2)),
                (Term::Var(a), Term::Var(b)) => Uni::ok_iff_atoms_match(a == b, src_id, target_id),
                (Term::Hole(a), Term::Hole(b)) => {
                    Uni::ok_iff_atoms_match(a == b, src_id, target_id)
                }
                (Term::Hole(a), _) => {
                    let sub = Sub::from_pairs([(a.0, target_id)]);
                    Uni::ok_with(sub, target_id)
                }
                (_, Term::Hole(b)) => {
                    let sub = Sub::from_pairs([(b.0, src_id)]);
                    Uni::ok_with(sub, src_id)
                }
                (Term::Lit(l1), Term::Lit(l2)) => {
                    Uni::ok_iff_atoms_match(self.lits_are_equal(l1, l2), src_id, target_id)
                }
                (Term::Access(a1), Term::Access(a2)) => {
                    let _ = self.unify_terms(a1.subject, a2.subject)?;
                    Uni::ok_iff_atoms_match(a1.field == a2.field, src_id, target_id)
                }
                (Term::FnCall(c1), Term::FnCall(c2)) => {
                    let _ = self.unify_terms(c1.subject, c2.subject)?;
                    let _ = self.unify_args(c1.args, c2.args)?;
                    Uni::ok(src_id)
                }
                (Term::FnRef(f1), Term::FnRef(f2)) => {
                    if f1 == f2 {
                        return Uni::ok(src_id);
                    }
                    let f1_def = self.get_fn_def(f1);
                    let f2_def = self.get_fn_def(f2);

                    self.context().enter_scope(f1.into(), || {
                        // @@Todo: use sub
                        let Uni { sub: param_sub, result: _ } = self.unify_params(
                            f1_def.ty.params,
                            f2_def.ty.params,
                            ParamOrigin::FnTy(f1_def.ty),
                        )?;

                        let return_ty_1_subbed =
                            self.sub_ops().apply_sub_to_ty(f1_def.ty.return_ty, &param_sub);
                        let return_ty_2_subbed =
                            self.sub_ops().apply_sub_to_ty(f2_def.ty.return_ty, &param_sub);

                        let Uni { result: _, sub: _ } =
                            self.unify_tys(return_ty_1_subbed, return_ty_2_subbed)?;

                        match (f1_def.body, f2_def.body) {
                            (FnBody::Defined(f1_body), FnBody::Defined(f2_body)) => {
                                let body_1_subbed =
                                    self.sub_ops().apply_sub_to_term(f1_body, &param_sub);
                                let body_2_subbed =
                                    self.sub_ops().apply_sub_to_term(f2_body, &param_sub);

                                let _ = self.unify_terms(body_1_subbed, body_2_subbed)?;
                                Uni::ok(src_id)
                            }
                            (FnBody::Intrinsic(i1), FnBody::Intrinsic(i2)) => {
                                Uni::ok_iff_atoms_match(i1.0 == i2.0, src_id, target_id)
                            }
                            (FnBody::Axiom, FnBody::Axiom) => Uni::ok(src_id),
                            _ => Uni::mismatch_atoms(src_id, target_id),
                        }
                    })
                }

                (Term::Match(m1), Term::Match(m2)) => {
                    let _ = self.unify_terms(m1.subject, m2.subject)?;

                    Uni::ok(src_id)
                }

                _ => Uni::mismatch_atoms(src_id, target_id),
            },
        }?;
        self.stores().location().copy_location(src_id, result.result);
        Ok(result)
    }

    pub fn pats_are_equal(&self, src_id: PatId, target_id: PatId) -> bool {
        match (self.get_pat(src_id), self.get_pat(target_id)) {
            (Pat::Binding(v1), Pat::Binding(v2)) => {
                v1.is_mutable == v2.is_mutable && v1.name == v2.name
            }
            (_, Pat::Binding(_)) | (Pat::Binding(_), _) => false,

            (Pat::Range(r1), Pat::Range(r2)) => {
                self.lits_are_equal(r1.start.into(), r2.start.into())
                    && self.lits_are_equal(r1.end.into(), r2.end.into())
                    && r1.range_end == r2.range_end
            }
            (Pat::Range(_), _) | (_, Pat::Range(_)) => false,

            (Pat::Lit(l1), Pat::Lit(l2)) => self.lits_are_equal(l1.into(), l2.into()),
            (Pat::Lit(_), _) | (_, Pat::Lit(_)) => false,

            (Pat::Tuple(t1), Pat::Tuple(t2)) => {
                self.pat_args_are_equal(t1.data, t2.data) && t1.data_spread == t2.data_spread
            }
            (Pat::Tuple(_), _) | (_, Pat::Tuple(_)) => false,

            (Pat::Array(a1), Pat::Array(a2)) => {
                self.pat_lists_are_equal(a1.pats, a2.pats) && a1.spread == a2.spread
            }
            (Pat::Array(_), _) | (_, Pat::Array(_)) => false,

            (Pat::Ctor(c1), Pat::Ctor(c2)) => {
                todo!()
            }
            (Pat::Ctor(_), _) | (_, Pat::Ctor(_)) => todo!(),
            (Pat::Or(_), Pat::Or(_)) => todo!(),
            (Pat::Or(_), _) | (_, Pat::Or(_)) => todo!(),
            (Pat::If(_), Pat::If(_)) => todo!(),
            (Pat::If(_), _) | (_, Pat::If(_)) => todo!(),
        }
    }

    /// Reduce an iterator of unifications into a single unification.
    ///
    /// If any of the unifications are blocked or error, then this is forwarded
    /// to the result.
    pub fn reduce_unifications<U, V>(
        &self,
        unifications: impl Iterator<Item = TcResult<Uni<U>>>,
        collect_results: impl FnOnce(Vec<U>) -> V,
    ) -> TcResult<Uni<V>> {
        let mut sub = Sub::identity();
        let mut results = Vec::new();

        for unification in unifications {
            let uni = unification?;
            sub = sub.join(&uni.sub);
            results.push(uni.result);
        }

        Uni::ok_with(sub, collect_results(results))
    }

    /// Unify two parameter lists, creating a substitution of holes.
    ///
    /// The parameters must be already in scope.
    ///
    /// Names are taken from target
    pub fn unify_params(
        &self,
        src_id: ParamsId,
        target_id: ParamsId,
        _origin: ParamOrigin,
    ) -> TcResult<Uni<ParamsId>> {
        self.param_ops().validate_params(src_id)?;
        self.param_ops().validate_params(target_id)?;

        if src_id.len() != target_id.len() {
            return Err(TcError::WrongParamLength {
                given_params_id: src_id,
                annotation_params_id: target_id,
            });
        }

        let name_sub = self.sub_ops().create_sub_from_param_names(src_id, target_id);

        let param_uni = self.reduce_unifications(
            src_id.iter().zip(target_id.iter()).map(|(src, target)| {
                let src = self.stores().params().get_element(src);
                let target = self.stores().params().get_element(target);

                match (src.default, target.default) {
                    (None, None) => {}
                    // @@Todo
                    _ => unimplemented!("unify_params with defaults"),
                }

                match (self.get_param_name_ident(src.id), self.get_param_name_ident(target.id)) {
                    (Some(name_a), Some(name_b)) if name_a != name_b => {
                        return Err(TcError::ParamMatch(ParamError::ParamNameMismatch {
                            param_a: src.id,
                            param_b: target.id,
                        }));
                    }
                    _ => {}
                }

                let Inference(target_ty, _) =
                    self.infer_ops().infer_ty(target.ty, self.new_ty_hole())?;

                // Apply the name substitution to the parameter
                let subbed_src_ty = self.sub_ops().apply_sub_to_ty(src.ty, &name_sub);

                let Inference(src_ty, _) =
                    self.infer_ops().infer_ty(subbed_src_ty, self.new_ty_hole())?;

                let unified_param = self.unify_tys(src_ty, target_ty)?.map_result(|ty| ParamData {
                    name: target.name,
                    ty,
                    default: None,
                });

                self.context_utils().add_param_binding(target.id);

                Ok(unified_param)
            }),
            |param_data| self.param_utils().create_params(param_data.into_iter()),
        )?;

        Ok(Uni { result: param_uni.result, sub: param_uni.sub.join(&name_sub) })
    }

    pub fn pat_lists_are_equal(&self, src_id: PatListId, target_id: PatListId) -> bool {
        if src_id.len() != target_id.len() {
            false
        } else {
            self.map_pat_list(src_id, |src| {
                self.map_pat_list(target_id, |target| {
                    src.iter()
                        .zip(target.iter())
                        .map(|(src, target)| match (src, target) {
                            (PatOrCapture::Pat(src_pat), PatOrCapture::Pat(target_pat)) => {
                                self.pats_are_equal(*src_pat, *target_pat)
                            }
                            (PatOrCapture::Capture, PatOrCapture::Capture) => true,
                            _ => false,
                        })
                        .all(|x| x)
                })
            })
        }
    }

    /// Unify two pattern argument lists, creating a substitution of holes.
    pub fn pat_args_are_equal(&self, src_id: PatArgsId, target_id: PatArgsId) -> bool {
        if src_id.len() != target_id.len() {
            false
        } else {
            self.map_pat_args(src_id, |src| {
                self.map_pat_args(target_id, |target| {
                    src.iter()
                        .zip(target.iter())
                        .map(|(src, target)| match (src.pat, target.pat) {
                            (PatOrCapture::Pat(src_pat), PatOrCapture::Pat(target_pat)) => {
                                self.pats_are_equal(src_pat, target_pat)
                            }
                            (PatOrCapture::Capture, PatOrCapture::Capture) => true,
                            _ => false,
                        })
                        .all(|x| x)
                })
            })
        }
    }

    pub fn unify_args(&self, src_id: ArgsId, target_id: ArgsId) -> TcResult<Uni<ArgsId>> {
        if src_id.len() != target_id.len() {
            return Err(TcError::DifferentParamOrArgLengths {
                a: src_id.into(),
                b: target_id.into(),
            });
        }
        self.map_args(src_id, |src| {
            self.map_args(target_id, |target| {
                self.reduce_unifications(
                    src.iter()
                        .zip(target.iter())
                        // @@Correctness: which name to use here?
                        .map(|(src, target)| {
                            Ok(self
                                .unify_terms(src.value, target.value)?
                                .map_result(|term| ArgData { target: target.target, value: term }))
                        }),
                    |arg_data| self.param_utils().create_args(arg_data.into_iter()),
                )
            })
        })
    }

    /// Whether two function types match in terms of their modality.
    pub fn fn_modalities_match(&self, f1: FnTy, f2: FnTy) -> bool {
        f1.implicit == f2.implicit && f1.is_unsafe == f2.is_unsafe && f1.pure == f2.pure
    }

    /// Determine whether two terms are equal.
    pub fn terms_are_equal(&self, t1: TermId, t2: TermId) -> bool {
        self.uni_ops().with_no_ctx().unify_terms(t1, t2).map(|result| result.sub.is_empty()).ok()
            == Some(true)
    }

    /// Determine whether the given type is uninhabitable.
    ///
    /// This does not look too deeply into the type, so it may return false
    /// for types that are actually uninhabitable.
    pub fn is_uninhabitable(&self, ty: TyId) -> TcResult<bool> {
        let ty = self.norm_ops().to_ty(self.norm_ops().normalise(ty.into())?);
        match self.get_ty(ty) {
            Ty::Data(data_ty) => {
                let data_def = self.stores().data_def().get(data_ty.data_def);
                match data_def.ctors {
                    DataDefCtors::Defined(ctors) => Ok(ctors.len() == 0),
                    DataDefCtors::Primitive(_) => Ok(false),
                }
            }
            _ => Ok(false),
        }
    }
}
