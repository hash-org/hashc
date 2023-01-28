//! Operations for unifying types and terms.

use derive_more::{Constructor, Deref};
use hash_tir::new::{
    args::ArgsId,
    defs::{DefArgsId, DefParamsId},
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

#[derive(Debug, Clone)]
pub enum Unification {
    Successful(Sub),
    Blocked,
}

impl Unification {
    pub fn map(self, f: impl FnOnce(Sub) -> Sub) -> Self {
        match self {
            Unification::Successful(sub) => Unification::Successful(f(sub)),
            Unification::Blocked => Unification::Blocked,
        }
    }

    pub fn and_then(self, f: impl FnOnce(Sub) -> TcResult<Unification>) -> TcResult<Unification> {
        match self {
            Unification::Successful(sub) => f(sub),
            Unification::Blocked => Ok(Unification::Blocked),
        }
    }
}

#[derive(Constructor, Deref)]
pub struct UnificationOps<'a, T: AccessToTypechecking>(&'a T);

impl<T: AccessToTypechecking> UnificationOps<'_, T> {
    fn ok(&self) -> TcResult<Unification> {
        Ok(Unification::Successful(Sub::identity()))
    }

    fn ok_with(&self, sub: Sub) -> TcResult<Unification> {
        Ok(Unification::Successful(sub))
    }

    fn blocked(&self) -> TcResult<Unification> {
        Ok(Unification::Blocked)
    }

    fn mismatch_types(&self, src_id: TyId, target_id: TyId) -> TcResult<Unification> {
        Err(TcError::MismatchingTypes { expected: target_id, actual: src_id })
    }

    fn ok_iff(&self, cond: bool, src_id: TyId, target_id: TyId) -> TcResult<Unification> {
        if cond {
            self.ok()
        } else {
            self.mismatch_types(src_id, target_id)
        }
    }

    /// Unify two types.
    pub fn unify_tys(&self, src_id: TyId, target_id: TyId) -> TcResult<Unification> {
        let src = self.get_ty(src_id);
        let target = self.get_ty(target_id);

        match (src, target) {
            // @@Todo: eval fully
            (Ty::Eval(term), _) => match self.use_term_as_ty(term) {
                Some(ty) => self.unify_tys(ty, target_id),
                _ => self.mismatch_types(src_id, target_id),
            },
            (_, Ty::Eval(term)) => match self.use_term_as_ty(term) {
                Some(ty) => self.unify_tys(src_id, ty),
                _ => self.mismatch_types(src_id, target_id),
            },

            (Ty::Hole(a), Ty::Hole(b)) => {
                if a == b {
                    // No-op
                    self.ok()
                } else {
                    // We can't unify two holes, so we have to block
                    self.blocked()
                }
            }
            (Ty::Hole(a), _) => {
                let sub = Sub::from_pairs([(a, self.new_term(target_id))]);
                self.ok_with(sub)
            }
            (_, Ty::Hole(b)) => {
                let sub = Sub::from_pairs([(b, self.new_term(src_id))]);
                self.ok_with(sub)
            }

            (Ty::Var(a), Ty::Var(b)) => self.ok_iff(a == b, src_id, target_id),
            (Ty::Var(_), _) | (_, Ty::Var(_)) => self.mismatch_types(src_id, target_id),

            (Ty::Tuple(t1), Ty::Tuple(t2)) => self.unify_params(t1.data, t2.data),
            (Ty::Tuple(_), _) | (_, Ty::Tuple(_)) => self.mismatch_types(src_id, target_id),

            (Ty::Fn(f1), Ty::Fn(f2)) => {
                if f1.implicit != f2.implicit
                    || f1.is_unsafe != f2.is_unsafe
                    || f1.pure != f2.pure
                    || f1.params.len() != f2.params.len()
                {
                    self.mismatch_types(src_id, target_id)
                } else {
                    // @@Todo: dependent
                    self.unify_params(f1.params, f2.params)?.and_then(|sub| {
                        let return_ty_1_subbed =
                            self.substitution_ops().apply_sub_to_ty(f1.return_ty, &sub);
                        let return_ty_2_subbed =
                            self.substitution_ops().apply_sub_to_ty(f2.return_ty, &sub);
                        let unify_return =
                            self.unify_tys(return_ty_1_subbed, return_ty_2_subbed)?;

                        unify_return.and_then(|return_sub| self.ok_with(sub.join(&return_sub)))
                    })
                }
            }
            (Ty::Fn(_), _) | (_, Ty::Fn(_)) => self.mismatch_types(src_id, target_id),

            (Ty::Ref(r1), Ty::Ref(r2)) => {
                if r1.mutable == r2.mutable && r1.kind == r2.kind {
                    self.unify_tys(r1.ty, r2.ty)
                } else {
                    self.mismatch_types(src_id, target_id)
                }
            }
            (Ty::Ref(_), _) | (_, Ty::Ref(_)) => self.mismatch_types(src_id, target_id),

            (Ty::Data(d1), Ty::Data(d2)) => {
                if d1.data_def == d2.data_def {
                    self.unify_def_args(d1.args, d2.args)
                } else {
                    self.mismatch_types(src_id, target_id)
                }
            }
            (Ty::Data(_), _) | (_, Ty::Data(_)) => self.mismatch_types(src_id, target_id),

            (Ty::Universe(u1), Ty::Universe(u2)) => {
                self.ok_iff(u1.size == u2.size, src_id, target_id)
            }
        }
    }

    /// Unify two terms.
    ///
    /// Unless these are types, they must be definitionally (up to beta
    /// reduction) equal.
    pub fn unify_terms(&self, src_id: TermId, target_id: TermId) -> TcResult<Unification> {
        let src = self.get_term(src_id);
        let target = self.get_term(target_id);

        let mismatch = || Err(TcError::UndecidableEquality { a: src_id, b: target_id });
        let ok_iff = |cond| if cond { self.ok() } else { mismatch() };

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
        unifications: impl Iterator<Item = TcResult<Unification>>,
    ) -> TcResult<Unification> {
        let mut sub = Sub::identity();
        for unification in unifications {
            match unification? {
                Unification::Successful(sub2) => {
                    sub = sub.join(&sub2);
                }
                Unification::Blocked => return Ok(Unification::Blocked),
            }
        }
        Ok(Unification::Successful(sub))
    }

    /// Unify two parameter lists, creating a substitution of holes.
    pub fn unify_params(&self, src_id: ParamsId, target_id: ParamsId) -> TcResult<Unification> {
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

    /// Unify two definition parameter lists, creating a substitution of holes.
    pub fn unify_def_params(&self, src: DefParamsId, target: DefParamsId) -> TcResult<Unification> {
        // @@Todo: dependent
        self.map_def_params(src, |src| {
            self.map_def_params(target, |target| {
                self.reduce_unifications(
                    src.iter()
                        .zip(target.iter())
                        .map(|(src, target)| self.unify_params(src.params, target.params)),
                )
            })
        })
    }

    /// Unify two definition argument lists, creating a substitution of holes.
    pub fn unify_def_args(&self, src: DefArgsId, target: DefArgsId) -> TcResult<Unification> {
        // @@Todo: dependent
        self.map_def_args(src, |src| {
            self.map_def_args(target, |target| {
                self.reduce_unifications(
                    src.iter()
                        .zip(target.iter())
                        .map(|(src, target)| self.unify_args(src.args, target.args)),
                )
            })
        })
    }

    /// Unify two argument lists, creating a substitution of holes.
    pub fn unify_args(&self, src_id: ArgsId, target_id: ArgsId) -> TcResult<Unification> {
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
