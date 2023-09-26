use hash_tir::tir::{TyId, UniverseTy};

use crate::{
    checker::Checker,
    env::TcEnv,
    operations::{
        normalisation::{already_normalised, NormalisationOptions},
        unification::unified,
        Operations,
    },
};

impl<E: TcEnv> Operations<UniverseTy> for Checker<'_, E> {
    type TyNode = TyId;
    type Node = TyId;

    fn check(
        &self,
        _: &mut hash_tir::context::Context,
        _: &mut UniverseTy,
        item_ty: Self::TyNode,
        _: Self::Node,
    ) -> crate::operations::checking::CheckResult {
        // Type: Type
        self.check_is_universe(item_ty)
    }

    fn normalise(
        &self,
        _: &mut hash_tir::context::Context,
        _opts: &NormalisationOptions,
        _: &mut UniverseTy,
        _: Self::Node,
    ) -> crate::operations::normalisation::NormaliseResult<()> {
        already_normalised()
    }

    fn unify(
        &self,
        _: &mut hash_tir::context::Context,
        _: &crate::operations::unification::UnificationOptions,
        _: &mut UniverseTy,
        _: &mut UniverseTy,
        _: Self::Node,
        _: Self::Node,
    ) -> crate::operations::unification::UnifyResult {
        unified()
    }

    fn substitute(&self, _: &hash_tir::sub::Sub, _: &mut UniverseTy) {}
}