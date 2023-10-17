use std::ops::ControlFlow;

use hash_storage::store::statics::StoreId;
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::HasContext,
    intrinsics::{definitions::bool_ty, utils::bool_term},
    tir::{
        IfPat, NodeId, NodeOrigin, NodesId, OrPat, Pat, PatId, PatListId, PatOrCapture, Term,
        TermId, Ty, TyId,
    },
};

use crate::{
    diagnostics::TcResult,
    env::TcEnv,
    options::normalisation::{normalise_nested, NormaliseResult},
    tc::Tc,
    traits::{OperationsOn, OperationsOnNode},
};

impl<E: TcEnv> Tc<'_, E> {
    /// Infer the given pattern list as one type.
    ///
    /// Returns the inferred list, and its inferred type.
    pub fn check_unified_pat_list(
        &self,
        pat_list_id: PatListId,
        element_annotation_ty: TyId,
    ) -> TcResult<()> {
        for pat in pat_list_id.elements().value() {
            match pat {
                PatOrCapture::Pat(pat) => {
                    self.check_node(pat, (element_annotation_ty, None))?;
                }
                PatOrCapture::Capture(_) => {}
            }
        }
        Ok(())
    }
}

impl<E: TcEnv> OperationsOnNode<PatId> for Tc<'_, E> {
    type AnnotNode = (TyId, Option<TermId>);

    fn check_node(
        &self,
        pat_id: PatId,
        (annotation_ty, binds_to): Self::AnnotNode,
    ) -> crate::diagnostics::TcResult<()> {
        self.register_new_atom(pat_id, annotation_ty);

        match *pat_id.value() {
            Pat::Binding(mut var) => self.check(&mut var, (annotation_ty, binds_to), pat_id)?,
            Pat::Range(mut range_pat) => self.check(&mut range_pat, annotation_ty, pat_id)?,
            Pat::Lit(lit) => self.check_node(*lit, annotation_ty)?,
            Pat::Tuple(mut tuple_pat) => self.check(&mut tuple_pat, annotation_ty, pat_id)?,
            Pat::Array(mut list_term) => self.check(&mut list_term, annotation_ty, pat_id)?,
            Pat::Ctor(mut ctor_pat) => self.check(&mut ctor_pat, annotation_ty, pat_id)?,
            Pat::Or(mut or_pat) => self.check(&mut or_pat, annotation_ty, pat_id)?,
            Pat::If(mut if_pat) => self.check(&mut if_pat, annotation_ty, pat_id)?,
        };

        self.register_atom_inference(pat_id, pat_id, annotation_ty);
        Ok(())
    }

    fn try_normalise_node(&self, _: PatId) -> NormaliseResult<ControlFlow<PatId>> {
        normalise_nested()
    }

    fn unify_nodes(&self, src: PatId, target: PatId) -> crate::diagnostics::TcResult<()> {
        // @@Todo: unification of patterns
        self.mismatching_atoms(src, target)
    }
}

impl<E: TcEnv> OperationsOn<IfPat> for Tc<'_, E> {
    type AnnotNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        pat: &mut IfPat,
        annotation_ty: Self::AnnotNode,
        _: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        self.check_node(pat.pat, (annotation_ty, None))?;
        let expected_condition_ty = Ty::expect_is(pat.condition, bool_ty(NodeOrigin::Expected));
        self.check_node(pat.condition, expected_condition_ty)?;
        if let Term::Var(v) = *pat.condition.value() {
            self.context().add_assignment(
                v.symbol,
                expected_condition_ty,
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
        self.check_unified_pat_list(pat.alternatives, annotation_ty)?;
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
        _src: &mut OrPat,
        _target: &mut OrPat,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> crate::diagnostics::TcResult<()> {
        // @@Todo: unification of patterns
        self.mismatching_atoms(src_node, target_node)
    }
}
