use hash_tir::tir::{TermId, TyId};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::TcResult,
    operations::{
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        OperationsOnNode,
    },
};

impl<E: TcEnv> OperationsOnNode<TermId> for Tc<'_, E> {
    type TyNode = TyId;

    fn check_node(&self, _item: TermId, _item_ty: Self::TyNode) -> TcResult<()> {
        todo!()
    }

    fn normalise_node(
        &self,

        _opts: &NormalisationOptions,
        _item: TermId,
    ) -> NormaliseResult<TermId> {
        todo!()
    }

    fn unify_nodes(
        &self,

        _opts: &UnificationOptions,
        _src: TermId,
        _target: TermId,
    ) -> TcResult<()> {
        todo!()
    }

    fn substitute_node(&self, _sub: &hash_tir::sub::Sub, _target: TermId) {
        todo!()
    }
}
