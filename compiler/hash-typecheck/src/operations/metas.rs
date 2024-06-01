use std::ops::ControlFlow;

use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    context::HasContext,
    tir::{
        ArgsId, CallTerm, FnDef, FnTy, Meta, Node, NodeId, NodeOrigin, Param, Term, TermId, TyId,
    },
};

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{already_normalised, normalised_to, NormaliseResult},
    tc::Tc,
    traits::OperationsOn,
};

#[derive(Debug, Clone)]
pub(crate) struct MetaCall {
    pub meta: Meta,
    pub args: ArgsId,
}

impl<E: TcEnv> Tc<'_, E> {
    pub(crate) fn classify_meta_call(&self, term: Term) -> Option<MetaCall> {
        match term {
            Term::Call(CallTerm { subject, args, .. }) => match subject.value().data {
                Term::Meta(meta) => Some(MetaCall { meta, args }),
                _ => None,
            },
            _ => None,
        }
    }

    /// Solve a pattern unification problem.
    /// @@Todo @@Docs
    pub(crate) fn solve(
        &self,
        meta_call: MetaCall,
        rhs: TermId,
        src_id: TermId,
        target_id: TermId,
    ) -> TcResult<()> {
        let mut args_vars = Vec::new();
        for arg in meta_call.args.iter() {
            match arg.value().value.value().data {
                Term::Var(v) => {
                    args_vars.push(v);
                }
                _ => return self.mismatching_atoms(src_id, target_id),
            }
        }

        let solution = Term::from(
            Node::create_at(
                FnDef {
                    ty: FnTy {
                        implicit: false,
                        pure: true,
                        is_unsafe: false,
                        params: Param::seq_positional(
                            args_vars.iter().map(|arg| self.context().get_binding_ty(arg.symbol)),
                            NodeOrigin::Generated,
                        ),
                        return_ty: self.fresh_meta(rhs.origin().inferred()),
                    },
                    name: meta_call.meta.name(),
                    body: rhs,
                },
                NodeOrigin::Generated,
            ),
            NodeOrigin::Generated,
        );
        self.solve_meta(meta_call.meta, solution);
        Ok(())
    }

    /// Fill metas in a term with their solutions.
    /// This is shallow.
    pub(crate) fn resolve_metas(&self, term: TermId) -> TermId {
        match term.value().data {
            Term::Meta(meta) => self.get_meta(meta).map(|s| self.resolve_metas(s)).unwrap_or(term),
            _ => term,
        }
    }
}

impl<E: TcEnv> OperationsOn<Meta> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        item: &mut Meta,
        _item_ty: Self::AnnotNode,
        item_node: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        // For each hole, generate a new meta
        match item {
            Meta::Hole(h) => {
                item_node.set(self.fresh_meta(h.origin().inferred()).value());
            }
            Meta::Generated(_) => {}
        }
        Ok(())
    }

    fn try_normalise(&self, meta: Meta, _: Self::Node) -> NormaliseResult<ControlFlow<Self::Node>> {
        match self.get_meta(meta) {
            Some(solution) => normalised_to(solution),
            None => already_normalised(),
        }
    }

    fn unify(
        &self,
        h1: &mut Meta,
        h2: &mut Meta,
        src_id: Self::Node,
        target_id: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        if h1 == h2 {
            Ok(())
        } else {
            // We can't unify two holes, so we have to block
            self.unification_blocked(src_id, target_id)
        }
    }
}
