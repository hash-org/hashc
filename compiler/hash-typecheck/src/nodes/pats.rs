use hash_storage::store::statics::StoreId;
use hash_tir::{
    atom_info::ItemInAtomInfo,
    intrinsics::{definitions::bool_ty, utils::bool_term},
    tir::{IfPat, NodeId, NodeOrigin, OrPat, Pat, PatId, Term, TermId, Ty, TyId},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    operations::{Operations, OperationsOnNode},
};

impl<E: TcEnv> Operations<IfPat> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        pat: &mut IfPat,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> crate::errors::TcResult<()> {
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

    fn normalise(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: IfPat,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut IfPat,
        _target: &mut IfPat,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut IfPat) {
        todo!()
    }
}

impl<E: TcEnv> Operations<OrPat> for Tc<'_, E> {
    type TyNode = TyId;
    type Node = PatId;

    fn check(
        &self,
        pat: &mut OrPat,
        annotation_ty: Self::TyNode,
        _: Self::Node,
    ) -> crate::errors::TcResult<()> {
        self.infer_unified_pat_list(pat.alternatives, annotation_ty)?;
        Ok(())
    }

    fn normalise(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: OrPat,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<Self::Node> {
        todo!()
    }

    fn unify(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut OrPat,
        _target: &mut OrPat,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut OrPat) {
        todo!()
    }
}

impl<E: TcEnv> OperationsOnNode<PatId> for Tc<'_, E> {
    type TyNode = (TyId, Option<TermId>);

    fn check_node(
        &self,
        pat_id: PatId,
        (annotation_ty, binds_to): Self::TyNode,
    ) -> crate::errors::TcResult<()> {
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

    fn normalise_node(
        &self,
        _opts: &crate::operations::normalisation::NormalisationOptions,
        _item: PatId,
    ) -> crate::operations::normalisation::NormaliseResult<PatId> {
        todo!()
    }

    fn unify_nodes(
        &self,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: PatId,
        _target: PatId,
    ) -> crate::errors::TcResult<()> {
        todo!()
    }

    fn substitute_node(&self, _sub: &hash_tir::sub::Sub, _target: PatId) {
        todo!()
    }
}
