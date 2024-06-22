use std::ops::ControlFlow;

use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    atom_info::ItemInAtomInfo, context::HasContext, tir::{
        ArgsId, CallTerm, FnDef, FnTy, Meta, Node, NodeId, NodeOrigin, Param, Term, TermId, TyId,
    }
};

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{already_normalised, normalised_to, NormaliseResult},
    tc::Tc,
    traits::OperationsOn,
};

#[derive(Debug, Clone, Copy)]
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

        self.normalise_node_in_place_no_signals(rhs)?;

        let fn_ty = FnTy {
            implicit: false,
            pure: true,
            is_unsafe: false,
            params: Param::seq(
                args_vars
                    .iter()
                    .map(|arg| (arg.symbol, Term::fresh_hole(arg.symbol.origin().inferred()))),
                NodeOrigin::Generated,
            ),
            return_ty: Term::fresh_hole(rhs.origin().inferred()),
        };

        let solution_fn =
            Node::create_at(
                FnDef { ty: fn_ty, name: meta_call.meta.name(), body: rhs },
                NodeOrigin::Generated,
            );

        let solution = Term::from(
            solution_fn,
            NodeOrigin::Generated,
        );

        self.register_atom_inference(solution_fn, solution_fn, fn_ty);
        self.register_atom_inference(solution, solution, Term::from(fn_ty, NodeOrigin::Generated));

        self.solve_meta(meta_call.meta, solution);
        Ok(())
    }

    /// Fill metas in a term with their solutions.
    ///
    /// Returns the
    /// This is shallow.
    pub(crate) fn resolve_metas_and_vars(&self, term: TermId) -> (TermId, Option<MetaCall>) {
        match self.classify_meta_call(term.value().data) {
            Some(call) => {
                let resolved = self.get_meta(call.meta).map(|s| self.resolve_metas_and_vars(s));
                match resolved {
                    Some(resolved) => (
                        self.normalise_node_no_signals(Term::from(
                            CallTerm { subject: resolved.0, args: call.args, implicit: false },
                            term.origin(),
                        ))
                        .unwrap(),
                        None,
                    ),
                    None => (term, Some(call)),
                }
            }
            None => match *term.value() {
                Term::Var(v) => {
                    if let Some(val) = self.context.try_get_decl_value(v.symbol) {
                        match val.value().data {
                            Term::Var(v_p) if v_p.symbol == v.symbol => (term, None),
                            _ => self.resolve_metas_and_vars(val),
                        }
                    } else {
                        (term, None)
                    }
                }
                _ => (term, None),
            },
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
            Meta::Generated(_) => {
                // panic!("Generated metas should not be checked: {}", item);
            }
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
