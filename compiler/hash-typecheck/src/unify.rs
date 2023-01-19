//! Operations for unifying types and terms.

use hash_tir::new::{
    args::ArgsId,
    defs::{DefArgsId, DefParamsId},
    params::ParamsId,
    terms::{Term, TermId},
    tys::{Ty, TyId},
    utils::common::CommonUtils,
};
use hash_utils::store::SequenceStoreKey;

use crate::{
    errors::{TcError, TcResult},
    subs::Sub,
    substitutions::SubstituteOps,
    AccessToTypechecking,
};

pub struct Unification {
    pub sub: Sub,
}

pub(super) trait UnifyOps: AccessToTypechecking {
    /// Unify two types.
    fn unify_tys(&self, src_id: TyId, target_id: TyId) -> TcResult<Unification> {
        let src = self.get_ty(src_id);
        let target = self.get_ty(target_id);

        let ok = || Ok(Unification { sub: Sub::identity() });
        let ok_with = |sub: Sub| Ok(Unification { sub });
        let mismatch = || Err(TcError::MismatchingTypes { expected: target_id, actual: src_id });
        let ok_iff = |cond| if cond { ok() } else { mismatch() };

        match (src, target) {
            // @@Todo: eval fully
            (Ty::Eval(term), _) => match self.use_term_as_ty(term) {
                Some(ty) => self.unify_tys(ty, target_id),
                _ => mismatch(),
            },
            (_, Ty::Eval(term)) => match self.use_term_as_ty(term) {
                Some(ty) => self.unify_tys(src_id, ty),
                _ => mismatch(),
            },

            (Ty::Hole(a), Ty::Hole(b)) => {
                if a == b {
                    // No-op
                    ok()
                } else {
                    let sub = Sub::from_pairs([(a, self.new_term(target_id))]);
                    ok_with(sub)
                }
            }
            (Ty::Hole(a), _) | (_, Ty::Hole(a)) => {
                let sub = Sub::from_pairs([(a, self.new_term(target_id))]);
                ok_with(sub)
            }

            (Ty::Var(a), Ty::Var(b)) => ok_iff(a == b),
            (Ty::Var(_), _) | (_, Ty::Var(_)) => mismatch(),

            (Ty::Tuple(t1), Ty::Tuple(t2)) => {
                let unify_inner = self.unify_params(t1.data, t2.data)?;
                ok_with(unify_inner.sub)
            }
            (Ty::Tuple(_), _) | (_, Ty::Tuple(_)) => mismatch(),

            (Ty::Fn(f1), Ty::Fn(f2)) => {
                if f1.implicit != f2.implicit
                    || f1.is_unsafe != f2.is_unsafe
                    || f1.pure != f2.pure
                    || f1.params.len() != f2.params.len()
                {
                    mismatch()
                } else {
                    // @@Todo: dependent
                    let unify_params = self.unify_params(f1.params, f2.params)?;
                    let return_ty_1_subbed = self.apply_sub_to_ty(f1.return_ty, &unify_params.sub);
                    let return_ty_2_subbed = self.apply_sub_to_ty(f2.return_ty, &unify_params.sub);
                    let unify_return = self.unify_tys(return_ty_1_subbed, return_ty_2_subbed)?;

                    ok_with(unify_params.sub.join(&unify_return.sub))
                }
            }
            (Ty::Fn(_), _) | (_, Ty::Fn(_)) => mismatch(),

            (Ty::Ref(r1), Ty::Ref(r2)) => {
                if r1.mutable == r2.mutable && r1.kind == r2.kind {
                    let unify_inner = self.unify_tys(r1.ty, r2.ty)?;
                    ok_with(unify_inner.sub)
                } else {
                    mismatch()
                }
            }
            (Ty::Ref(_), _) | (_, Ty::Ref(_)) => mismatch(),

            (Ty::Data(d1), Ty::Data(d2)) => {
                if d1.data_def == d2.data_def {
                    let unify_args = self.unify_def_args(d1.args, d2.args)?;
                    ok_with(unify_args.sub)
                } else {
                    mismatch()
                }
            }
            (Ty::Data(_), _) | (_, Ty::Data(_)) => mismatch(),

            (Ty::Universe(u1), Ty::Universe(u2)) => ok_iff(u1.size == u2.size),
        }
    }

    /// Unify two terms.
    ///
    /// Unless these are types, they must be definitionally (up to beta
    /// reduction) equal.
    fn unify_terms(&self, src_id: TermId, target_id: TermId) -> TcResult<Unification> {
        let src = self.get_term(src_id);
        let target = self.get_term(target_id);

        let ok = || Ok(Unification { sub: Sub::identity() });
        let mismatch = || Err(TcError::UndecidableEquality { a: src_id, b: target_id });
        let ok_iff = |cond| if cond { ok() } else { mismatch() };

        match (src, target) {
            (Term::Ty(t1), Term::Ty(t2)) => self.unify_tys(t1, t2),
            (Term::Var(a), Term::Var(b)) => ok_iff(a == b),
            (Term::Var(_), _) | (_, Term::Var(_)) => mismatch(),
            _ => mismatch(),
        }
    }

    /// Try to use the given term as a type.
    fn use_term_as_ty(&self, term: TermId) -> Option<TyId> {
        match self.get_term(term) {
            Term::Var(var) => Some(self.new_ty(var)),
            Term::Ty(ty) => Some(ty),
            _ => None,
        }
    }

    /// Unify two parameter lists, creating a substitution of holes.
    fn unify_params(&self, src_id: ParamsId, target_id: ParamsId) -> TcResult<Unification> {
        self.map_params(src_id, |src| {
            self.map_params(target_id, |target| {
                let mut sub = Sub::identity();
                for (src, target) in src.iter().zip(target.iter()) {
                    let unify_inner = self.unify_tys(src.ty, target.ty)?;
                    sub = sub.join(&unify_inner.sub);
                }
                Ok(Unification { sub })
            })
        })
    }

    /// Unify two definition parameter lists, creating a substitution of holes.
    fn unify_def_params(&self, src: DefParamsId, target: DefParamsId) -> TcResult<Unification> {
        // @@Todo: dependent
        self.map_def_params(src, |src| {
            self.map_def_params(target, |target| {
                let mut sub = Sub::identity();
                for (src, target) in src.iter().zip(target.iter()) {
                    let unify_inner = self.unify_params(src.params, target.params)?;
                    sub = sub.join(&unify_inner.sub);
                }
                Ok(Unification { sub })
            })
        })
    }

    /// Unify two definition argument lists, creating a substitution of holes.
    fn unify_def_args(&self, src: DefArgsId, target: DefArgsId) -> TcResult<Unification> {
        // @@Todo: dependent
        self.map_def_args(src, |src| {
            self.map_def_args(target, |target| {
                let mut sub = Sub::identity();
                for (src, target) in src.iter().zip(target.iter()) {
                    let unify_inner = self.unify_args(src.args, target.args)?;
                    sub = sub.join(&unify_inner.sub);
                }
                Ok(Unification { sub })
            })
        })
    }

    /// Unify two argument lists, creating a substitution of holes.
    fn unify_args(&self, src_id: ArgsId, target_id: ArgsId) -> TcResult<Unification> {
        self.map_args(src_id, |src| {
            self.map_args(target_id, |target| {
                let mut sub = Sub::identity();
                for (src, target) in src.iter().zip(target.iter()) {
                    let unify_inner = self.unify_terms(src.value, target.value)?;
                    sub = sub.join(&unify_inner.sub);
                }
                Ok(Unification { sub })
            })
        })
    }
}

impl<T: AccessToTypechecking> UnifyOps for T {}
