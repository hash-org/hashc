//! Operations for unifying types and terms.

use derive_more::{Constructor, Deref};
use hash_tir::new::{
    args::{ArgData, ArgsId},
    data::DataTy,
    environment::context::ParamOrigin,
    fns::FnTy,
    lits::{Lit, PrimTerm},
    params::{ParamData, ParamsId},
    sub::Sub,
    terms::{Term, TermId},
    tuples::TupleTy,
    tys::{Ty, TyId},
    utils::{common::CommonUtils, AccessToUtils},
};
use hash_utils::store::{SequenceStore, SequenceStoreKey};

use crate::{
    errors::{TcError, TcResult},
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
    pub fn blocked() -> TcResult<Self> {
        Err(TcError::Blocked)
    }

    /// Create a unification result that is an error of mismatching types.
    pub fn mismatch_types(src_id: TyId, target_id: TyId) -> TcResult<Self> {
        Err(TcError::MismatchingTypes { expected: target_id, actual: src_id, inferred_from: None })
    }

    /// Create a unification result that is an error of mismatching terms.
    pub fn mismatch_terms(src_id: TermId, target_id: TermId) -> TcResult<Self> {
        Err(TcError::UndecidableEquality { a: src_id, b: target_id })
    }

    pub fn map_result<U>(self, f: impl FnOnce(T) -> U) -> Uni<U> {
        Uni { result: f(self.result), sub: self.sub }
    }
}

impl Uni<TyId> {
    /// Create a unification result that is an error of mismatching types if
    /// `cond` is false, and successful otherwise.
    pub fn ok_iff_types_match(cond: bool, src_id: TyId, target_id: TyId) -> TcResult<Uni<TyId>> {
        if cond {
            Uni::ok(target_id)
        } else {
            Uni::mismatch_types(src_id, target_id)
        }
    }
}

impl Uni<TermId> {
    /// Create a unification result that is an error of mismatching terms if
    /// `cond` is false, and successful otherwise.
    pub fn ok_iff_terms_match(
        cond: bool,
        src_id: TermId,
        target_id: TermId,
    ) -> TcResult<Uni<TermId>> {
        if cond {
            Uni::ok(target_id)
        } else {
            Uni::mismatch_terms(src_id, target_id)
        }
    }
}

#[derive(Constructor, Deref)]
pub struct UnificationOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> UnificationOps<'_, T> {
    /// Unify two types.
    pub fn unify_tys(&self, src_id: TyId, target_id: TyId) -> TcResult<Uni<TyId>> {
        let src_id =
            self.normalisation_ops().to_ty(self.normalisation_ops().normalise(src_id.into())?);
        let target_id =
            self.normalisation_ops().to_ty(self.normalisation_ops().normalise(target_id.into())?);

        let src = self.get_ty(src_id);
        let target = self.get_ty(target_id);

        match (src, target) {
            (Ty::Data(data_ty), _) if data_ty.data_def == self.primitives().never() => {
                Uni::ok(target_id)
            }
            (Ty::Hole(a), Ty::Hole(b)) => {
                if a == b {
                    // No-op
                    Uni::ok(target_id)
                } else {
                    // We can't unify two holes, so we have to block
                    Uni::blocked()
                }
            }
            (Ty::Hole(a), _) => {
                let sub = Sub::from_pairs([(a.0, self.new_term(target_id))]);
                Uni::ok_with(sub, target_id)
            }
            (_, Ty::Hole(b)) => {
                let sub = Sub::from_pairs([(b.0, self.new_term(src_id))]);
                Uni::ok_with(sub, src_id)
            }

            // @@Todo: eval fully
            (Ty::Eval(t1), Ty::Eval(t2)) => {
                self.unify_terms(t1, t2).map(|result| result.map_result(|r| self.new_ty(r)))
            }
            (Ty::Eval(term), _) => match self
                .normalisation_ops()
                .maybe_to_ty(self.normalisation_ops().normalise(term.into())?)
            {
                Some(ty_id) => self.unify_tys(ty_id, target_id),
                // @@Todo: usage error
                _ => Uni::mismatch_types(src_id, target_id),
            },
            (_, Ty::Eval(term)) => match self
                .normalisation_ops()
                .maybe_to_ty(self.normalisation_ops().normalise(term.into())?)
            {
                Some(ty) => self.unify_tys(src_id, ty),
                // @@Todo: usage error
                _ => Uni::mismatch_types(src_id, target_id),
            },

            (Ty::Var(a), Ty::Var(b)) => Uni::ok_iff_types_match(a == b, src_id, target_id),
            (Ty::Var(_), _) | (_, Ty::Var(_)) => Uni::mismatch_types(src_id, target_id),

            (Ty::Tuple(t1), Ty::Tuple(t2)) => Ok(self
                .unify_params(t1.data, t2.data, ParamOrigin::TupleTy(t1))?
                .map_result(|data| self.new_ty(TupleTy { data }))),
            (Ty::Tuple(_), _) | (_, Ty::Tuple(_)) => Uni::mismatch_types(src_id, target_id),

            (Ty::Fn(f1), Ty::Fn(f2)) => {
                if !self.fn_modalities_match(f1, f2) {
                    Uni::mismatch_types(src_id, target_id)
                } else {
                    self.context().enter_scope(f2.into(), || {
                        let Uni { sub: param_sub, result: params } =
                            self.unify_params(f1.params, f2.params, ParamOrigin::FnTy(f1))?;

                        let return_ty_1_subbed =
                            self.substitution_ops().apply_sub_to_ty(f1.return_ty, &param_sub);
                        let return_ty_2_subbed =
                            self.substitution_ops().apply_sub_to_ty(f2.return_ty, &param_sub);

                        let Uni { result: return_ty, sub: return_ty_sub } =
                            self.unify_tys(return_ty_1_subbed, return_ty_2_subbed)?;

                        Ok(Uni {
                            result: self.new_ty(FnTy { return_ty, params, ..f1 }),
                            sub: return_ty_sub.join(&param_sub),
                        })
                    })
                }
            }
            (Ty::Fn(_), _) | (_, Ty::Fn(_)) => Uni::mismatch_types(src_id, target_id),

            (Ty::Ref(r1), Ty::Ref(r2)) => {
                if r1.mutable == r2.mutable && r1.kind == r2.kind {
                    self.unify_tys(r1.ty, r2.ty)
                } else {
                    Uni::mismatch_types(src_id, target_id)
                }
            }
            (Ty::Ref(_), _) | (_, Ty::Ref(_)) => Uni::mismatch_types(src_id, target_id),

            (Ty::Data(d1), Ty::Data(d2)) => {
                if d1.data_def == d2.data_def {
                    Ok(self
                        .unify_args(d1.args, d2.args)?
                        .map_result(|args| self.new_ty(DataTy { data_def: d1.data_def, args })))
                } else {
                    Uni::mismatch_types(src_id, target_id)
                }
            }
            (Ty::Data(_), _) | (_, Ty::Data(_)) => Uni::mismatch_types(src_id, target_id),

            (Ty::Universe(u1), Ty::Universe(u2)) => {
                Uni::ok_iff_types_match(u1.size == u2.size, src_id, target_id)
            }
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

        let src_id =
            self.normalisation_ops().to_term(self.normalisation_ops().normalise(src_id.into())?);
        let target_id =
            self.normalisation_ops().to_term(self.normalisation_ops().normalise(target_id.into())?);

        let src = self.get_term(src_id);
        let target = self.get_term(target_id);

        match (self.try_use_term_as_ty(src_id), self.try_use_term_as_ty(target_id)) {
            (Some(src_ty), Some(target_ty)) => {
                let uni = self.unify_tys(src_ty, target_ty)?;
                Ok(uni.map_result(|t| self.new_term(t)))
            }
            _ => match (src, target) {
                (Term::Ty(t1), _) => self.unify_terms(self.use_ty_as_term(t1), target_id),
                (_, Term::Ty(t2)) => self.unify_terms(src_id, self.use_ty_as_term(t2)),
                (Term::Var(a), Term::Var(b)) => Uni::ok_iff_terms_match(a == b, src_id, target_id),
                (Term::Hole(a), Term::Hole(b)) => {
                    Uni::ok_iff_terms_match(a == b, src_id, target_id)
                }
                (Term::Hole(a), _) => {
                    let sub = Sub::from_pairs([(a.0, target_id)]);
                    Uni::ok_with(sub, target_id)
                }
                (_, Term::Hole(b)) => {
                    let sub = Sub::from_pairs([(b.0, src_id)]);
                    Uni::ok_with(sub, src_id)
                }
                (Term::Prim(p1), Term::Prim(p2)) => match (p1, p2) {
                    (PrimTerm::Lit(l1), PrimTerm::Lit(l2)) => match (l1, l2) {
                        (Lit::Int(i1), Lit::Int(i2)) => {
                            Uni::ok_iff_terms_match(i1.value() == i2.value(), src_id, target_id)
                        }
                        (Lit::Str(s1), Lit::Str(s2)) => {
                            Uni::ok_iff_terms_match(s1.value() == s2.value(), src_id, target_id)
                        }
                        (Lit::Char(c1), Lit::Char(c2)) => {
                            Uni::ok_iff_terms_match(c1.value() == c2.value(), src_id, target_id)
                        }
                        (Lit::Float(f1), Lit::Float(f2)) => {
                            Uni::ok_iff_terms_match(f1.value() == f2.value(), src_id, target_id)
                        }
                        _ => Uni::mismatch_terms(src_id, target_id),
                    },
                    (PrimTerm::Array(_), PrimTerm::Array(_)) => todo!(),
                    _ => Uni::mismatch_terms(src_id, target_id),
                },
                _ => Uni::mismatch_terms(src_id, target_id),
            },
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
        origin: ParamOrigin,
    ) -> TcResult<Uni<ParamsId>> {
        self.param_ops().validate_params(src_id)?;
        self.param_ops().validate_params(target_id)?;

        if src_id.len() != target_id.len() {
            return Err(TcError::WrongParamLength {
                given_params_id: src_id,
                annotation_params_id: target_id,
            });
        }

        let name_sub = self.substitution_ops().create_sub_from_param_names(src_id, target_id);

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

                let (target_ty, _) =
                    self.inference_ops().infer_ty(target.ty, self.new_ty_hole())?;

                // Apply the name substitution to the parameter
                let subbed_src_ty = self.substitution_ops().apply_sub_to_ty(src.ty, &name_sub);

                let (src_ty, _) =
                    self.inference_ops().infer_ty(subbed_src_ty, self.new_ty_hole())?;

                let unified_param = self.unify_tys(src_ty, target_ty)?.map_result(|ty| ParamData {
                    name: target.name,
                    ty,
                    default: None,
                });

                self.context_utils().add_param_binding(target.id, origin);

                Ok(unified_param)
            }),
            |param_data| self.param_utils().create_params(param_data.into_iter()),
        )?;

        Ok(Uni { result: param_uni.result, sub: param_uni.sub.join(&name_sub) })
    }

    /// Unify two argument lists, creating a substitution of holes.
    pub fn unify_args(&self, src_id: ArgsId, target_id: ArgsId) -> TcResult<Uni<ArgsId>> {
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
}
