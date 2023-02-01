//! Operations for unifying types and terms.

use derive_more::{Constructor, Deref};
use hash_tir::new::{
    args::ArgsId,
    params::ParamsId,
    sub::Sub,
    terms::{Term, TermId},
    tys::{Ty, TyId},
    utils::common::CommonUtils,
};
use hash_utils::store::SequenceStoreKey;

use crate::{
    errors::{TcError, TcResult},
    AccessToTypechecking,
};

/// Represents a unification result.
///
/// For now, this is just a substitution, but kept as
/// a separate type to allow for future extensions.
#[derive(Debug, Clone)]
pub struct Uni {
    pub sub: Sub,
}

impl Uni {
    /// Create a unification result that is successful and has no substitution.
    pub fn ok() -> TcResult<Uni> {
        Ok(Uni { sub: Sub::identity() })
    }

    /// Create a unification result that is successful and has the given
    /// substitution.
    pub fn ok_with(sub: Sub) -> TcResult<Uni> {
        Ok(Uni { sub })
    }

    /// Create a unification result that is blocked.
    pub fn blocked() -> TcResult<Uni> {
        Err(TcError::Blocked)
    }

    /// Create a unification result that is an error of mismatching types.
    pub fn mismatch_types(src_id: TyId, target_id: TyId) -> TcResult<Uni> {
        Err(TcError::MismatchingTypes { expected: target_id, actual: src_id })
    }

    /// Create a unification result that is an error of mismatching types if
    /// `cond` is false, and successful otherwise.
    pub fn ok_iff(cond: bool, src_id: TyId, target_id: TyId) -> TcResult<Uni> {
        if cond {
            Self::ok()
        } else {
            Self::mismatch_types(src_id, target_id)
        }
    }
}

#[derive(Constructor, Deref)]
pub struct UnificationOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> UnificationOps<'_, T> {
    /// Unify two types.
    pub fn unify_tys(&self, src_id: TyId, target_id: TyId) -> TcResult<Uni> {
        let src = self.get_ty(src_id);
        let target = self.get_ty(target_id);

        match (src, target) {
            // @@Todo: eval fully
            (Ty::Eval(term), _) => match self.use_term_as_ty(term) {
                Some(ty) => self.unify_tys(ty, target_id),
                _ => Uni::mismatch_types(src_id, target_id),
            },
            (_, Ty::Eval(term)) => match self.use_term_as_ty(term) {
                Some(ty) => self.unify_tys(src_id, ty),
                _ => Uni::mismatch_types(src_id, target_id),
            },

            (Ty::Hole(a), Ty::Hole(b)) => {
                if a == b {
                    // No-op
                    Uni::ok()
                } else {
                    // We can't unify two holes, so we have to block
                    Uni::blocked()
                }
            }
            (Ty::Hole(a), _) => {
                let sub = Sub::from_pairs([(a, self.new_term(target_id))]);
                Uni::ok_with(sub)
            }
            (_, Ty::Hole(b)) => {
                let sub = Sub::from_pairs([(b, self.new_term(src_id))]);
                Uni::ok_with(sub)
            }

            (Ty::Var(a), Ty::Var(b)) => Uni::ok_iff(a == b, src_id, target_id),
            (Ty::Var(_), _) | (_, Ty::Var(_)) => Uni::mismatch_types(src_id, target_id),

            (Ty::Tuple(t1), Ty::Tuple(t2)) => self.unify_params(t1.data, t2.data),
            (Ty::Tuple(_), _) | (_, Ty::Tuple(_)) => Uni::mismatch_types(src_id, target_id),

            (Ty::Fn(f1), Ty::Fn(f2)) => {
                if f1.implicit != f2.implicit
                    || f1.is_unsafe != f2.is_unsafe
                    || f1.pure != f2.pure
                    || f1.params.len() != f2.params.len()
                {
                    Uni::mismatch_types(src_id, target_id)
                } else {
                    // @@Todo: dependent
                    let Uni { sub } = self.unify_params(f1.params, f2.params)?;
                    let return_ty_1_subbed =
                        self.substitution_ops().apply_sub_to_ty(f1.return_ty, &sub);
                    let return_ty_2_subbed =
                        self.substitution_ops().apply_sub_to_ty(f2.return_ty, &sub);
                    let Uni { sub: return_sub } =
                        self.unify_tys(return_ty_1_subbed, return_ty_2_subbed)?;
                    Uni::ok_with(sub.join(&return_sub))
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
                    self.unify_args(d1.args, d2.args)
                } else {
                    Uni::mismatch_types(src_id, target_id)
                }
            }
            (Ty::Data(_), _) | (_, Ty::Data(_)) => Uni::mismatch_types(src_id, target_id),

            (Ty::Universe(u1), Ty::Universe(u2)) => {
                Uni::ok_iff(u1.size == u2.size, src_id, target_id)
            }
        }
    }

    /// Unify two terms.
    ///
    /// Unless these are types, they must be definitionally (up to beta
    /// reduction) equal.
    pub fn unify_terms(&self, src_id: TermId, target_id: TermId) -> TcResult<Uni> {
        let src = self.get_term(src_id);
        let target = self.get_term(target_id);

        let mismatch = || Err(TcError::UndecidableEquality { a: src_id, b: target_id });
        let ok_iff = |cond| if cond { Uni::ok() } else { mismatch() };

        match (src, target) {
            (Term::Ty(t1), Term::Ty(t2)) => self.unify_tys(t1, t2),
            (Term::Var(a), Term::Var(b)) => ok_iff(a == b),
            (Term::Var(_), _) | (_, Term::Var(_)) => mismatch(),
            _ => mismatch(),
        }
    }

    /// Reduce an iterator of unifications into a single unification.
    ///
    /// If any of the unifications are blocked or error, then this is forwarded
    /// to the result.
    pub fn reduce_unifications(
        &self,
        unifications: impl Iterator<Item = TcResult<Uni>>,
    ) -> TcResult<Uni> {
        let mut sub = Sub::identity();
        for unification in unifications {
            sub = sub.join(&unification?.sub);
        }
        Uni::ok_with(sub)
    }

    /// Unify two parameter lists, creating a substitution of holes.
    pub fn unify_params(&self, src_id: ParamsId, target_id: ParamsId) -> TcResult<Uni> {
        self.map_params(src_id, |src| {
            self.map_params(target_id, |target| {
                self.reduce_unifications(
                    src.iter()
                        .zip(target.iter())
                        .map(|(src, target)| self.unify_tys(src.ty, target.ty)),
                )
            })
        })
    }

    /// Unify two argument lists, creating a substitution of holes.
    pub fn unify_args(&self, src_id: ArgsId, target_id: ArgsId) -> TcResult<Uni> {
        self.map_args(src_id, |src| {
            self.map_args(target_id, |target| {
                self.reduce_unifications(
                    src.iter()
                        .zip(target.iter())
                        .map(|(src, target)| self.unify_terms(src.value, target.value)),
                )
            })
        })
    }
}
