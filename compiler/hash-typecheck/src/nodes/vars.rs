use hash_tir::tir::{TermId, TyId, VarTerm};

use crate::{checker::Checker, env::TcEnv, operations::Operations};

impl<E: TcEnv> Operations<VarTerm> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TermId;

    fn check(
        &self,
        _ctx: &mut hash_tir::context::Context,
        _item: &mut VarTerm,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> crate::operations::checking::CheckResult {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut hash_tir::context::Context,
        _item: &mut VarTerm,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut hash_tir::context::Context,
        _src: &mut VarTerm,
        _target: &mut VarTerm,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::operations::unification::UnifyResult {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut VarTerm) {
        todo!()
    }
}
