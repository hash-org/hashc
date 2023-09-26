use hash_tir::tir::{TyId, UniverseTy};

use crate::{checker::Checker, env::TcEnv, operations::Operations};

impl<E: TcEnv> Operations<UniverseTy> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TyId;

    fn check(
        &self,
        _ctx: &mut hash_tir::context::Context,
        _item: &mut UniverseTy,
        _item_ty: Self::TyNode,
        _item_node: Self::Node,
    ) -> crate::operations::checking::CheckResult {
        todo!()
    }

    fn normalise(
        &self,
        _ctx: &mut hash_tir::context::Context,
        _item: &mut UniverseTy,
        _item_node: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<()> {
        todo!()
    }

    fn unify(
        &self,
        _ctx: &mut hash_tir::context::Context,
        _opts: &crate::operations::unification::UnificationOptions,
        _src: &mut UniverseTy,
        _target: &mut UniverseTy,
        _src_node: Self::Node,
        _target_node: Self::Node,
    ) -> crate::operations::unification::UnifyResult {
        todo!()
    }

    fn substitute(&self, _sub: &hash_tir::sub::Sub, _target: &mut UniverseTy) {
        todo!()
    }
}
