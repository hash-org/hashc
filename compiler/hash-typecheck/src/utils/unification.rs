use hash_tir::{
    context::{HasContext, ScopeKind},
    sub::Sub,
    tir::{SymbolId, TermId},
    visitor::{Atom, Map, Visit, Visitor},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::{TcError, TcResult},
    operations::OperationsOnNode,
};

impl<E: TcEnv> Tc<'_, E> {
    /// Add the given substitutions to the context.
    pub fn add_unification_from_sub(&self, sub: &Sub) {
        self.context().add_sub_to_scope(sub);
    }

    /// Add the given unification to the context, and create a substitution
    /// from it.
    pub fn add_unification(&self, src: SymbolId, target: TermId) -> Sub {
        let sub = Sub::from_pairs([(src, target)]);
        self.add_unification_from_sub(&sub);
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
                (Atom::Pat(a), Atom::Pat(b)) => Err(TcError::MismatchingPats { a, b }),
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
            (Atom::Term(a), Atom::Term(b)) => {
                Err(TcError::MismatchingTypes { expected: b, actual: a })
            }
            (Atom::FnDef(a), Atom::FnDef(b)) => Err(TcError::MismatchingFns { a, b }),
            (Atom::Pat(a), Atom::Pat(b)) => Err(TcError::MismatchingPats { a, b }),
            _ => unreachable!(),
        }
    }

    /// Unify the source and target and produce a substitution instead of adding
    /// it to the context.
    pub fn unify_self_contained<N: Copy>(&self, src_id: N, target_id: N) -> TcResult<(N, Sub)>
    where
        Self: OperationsOnNode<N>,
        Visitor: Visit<N> + Map<N>,
    {
        let initial = target_id;
        let sub = self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
            self.unify_nodes(src_id, target_id)?;
            Ok(self.sub_ops().create_sub_from_current_scope())
        })?;
        let subbed_initial = self.sub_ops().apply_sub(initial, &sub);
        self.add_unification_from_sub(&sub);
        Ok((subbed_initial, sub))
    }

    /// Determine whether two nodes are equal.
    pub fn nodes_are_equal<N: Copy>(&self, t1: N, t2: N) -> bool
    where
        Self: OperationsOnNode<N>,
    {
        self.unification_opts.modify_terms.enter(false, || {
            self.context().enter_scope(ScopeKind::Sub, || self.unify_nodes(t1, t2).is_ok())
        })
    }
}
