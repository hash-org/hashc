use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_tir::{
    context::HasContext,
    intrinsics::{definitions::bool_ty, utils::bool_term},
    tir::{IfPat, NodeId, NodeOrigin, OrPat, PatId, Term, Ty, TyId},
};

use crate::{
    env::TcEnv,
    options::normalisation::{normalise_nested, NormaliseResult},
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode, ScopedOperationsOnNode},
};

impl<E: TcEnv> OperationsOn<IfPat> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        pat: &mut IfPat,
        annotation_ty: Self::AnnotNode,
        _: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        self.check_node(pat.pat, annotation_ty)?;
        let expected_condition_ty = Ty::expect_is(pat.condition, bool_ty(NodeOrigin::Expected));
        self.check_node(pat.condition, expected_condition_ty)?;
        if let Term::Var(v) = *pat.condition.value() {
            self.context().add_assignment(
                v.symbol,
                bool_term(true, pat.condition.origin().inferred()),
            );
        }
        Ok(())
    }

    fn try_normalise(
        &self,
        _item: IfPat,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        normalise_nested()
    }

    fn unify(
        &self,
        src: &mut IfPat,
        target: &mut IfPat,
        _: Self::Node,
        _: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        self.unify_nodes(src.pat, target.pat)?;
        self.unify_nodes(src.condition, target.condition)
    }
}

impl<E: TcEnv> OperationsOn<OrPat> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        pat: &mut OrPat,
        annotation_ty: Self::AnnotNode,
        _: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        self.check_unified_args(pat.alternatives, annotation_ty)?;
        Ok(())
    }

    fn try_normalise(
        &self,
        _item: OrPat,
        _item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>> {
        normalise_nested()
    }

    fn unify(
        &self,
        src: &mut OrPat,
        target: &mut OrPat,
        _: Self::Node,
        _: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        self.unify_nodes(src.alternatives, target.alternatives)
    }
}
