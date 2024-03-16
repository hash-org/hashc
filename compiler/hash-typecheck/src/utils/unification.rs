//! General utilities for unifying TIR terms.
//!
//! These are used from within `unify` procedures in `Operations`.
use hash_tir::{
    context::{HasContext, ScopeKind},
    sub::Sub,
    tir::{SymbolId, TermId},
    visitor::Atom,
};

use crate::{
    diagnostics::{TcError, TcResult},
    env::TcEnv,
    tc::Tc,
    traits::OperationsOnNode,
};

impl<E: TcEnv> Tc<'_, E> {
    /// Add the given substitutions to the context.
    pub fn add_sub_to_scope(&self, sub: &Sub) {
        self.context().add_sub_to_scope(sub);
    }

    /// Add the given unification to the context, and create a substitution
    /// from it.
    pub fn add_unification(&self, src: SymbolId, target: TermId) -> Sub {
        let sub = Sub::from_pairs([(src, target)]);
        self.add_sub_to_scope(&sub);
        sub
    }

    /// Emit an error that the unification cannot continue because it is
    /// blocked.
    pub fn unification_blocked<U>(
        &self,
        src_id: impl Into<Atom>,
        target_id: impl Into<Atom>,
    ) -> TcResult<U> {
        Err(TcError::NeedMoreTypeAnnotationsToUnify {
            src: src_id.into(),
            target: target_id.into(),
        })
    }

    /// Emit an error that the two atoms are mismatching if `cond` is false,
    pub fn unification_ok_or_mismatching_atoms(
        &self,
        cond: bool,
        src_id: impl Into<Atom>,
        target_id: impl Into<Atom>,
    ) -> TcResult<()> {
        if cond {
            Ok(())
        } else {
            match (src_id.into(), target_id.into()) {
                (Atom::Term(a), Atom::Term(b)) => {
                    Err(TcError::MismatchingTypes { expected: b, actual: a })
                }
                (Atom::FnDef(a), Atom::FnDef(b)) => Err(TcError::MismatchingFns { a, b }),
                _ => unreachable!(),
            }
        }
    }

    /// Emit an error that the two atoms are mismatching.
    pub fn mismatching_atoms<U>(
        &self,
        src_id: impl Into<Atom>,
        target_id: impl Into<Atom>,
    ) -> TcResult<U> {
        match (src_id.into(), target_id.into()) {
            (Atom::Term(a), Atom::Term(b)) => Err(TcError::UndecidableEquality { a, b }),
            (Atom::FnDef(a), Atom::FnDef(b)) => Err(TcError::MismatchingFns { a, b }),
            _ => unreachable!(),
        }
    }

    /// Determine whether two nodes are equal, by unification.
    // @@Formalise/@@Fixme: we should specify what equality means precisely.
    // Additionally, we probably need bi-directional unification here.
    pub fn nodes_are_equal<N: Copy>(&self, t1: N, t2: N) -> bool
    where
        Self: OperationsOnNode<N>,
    {
        self.unification_opts.modify_terms.enter(false, || {
            self.context().enter_scope(ScopeKind::Sub, || self.unify_nodes(t1, t2).is_ok())
        })
    }
}
