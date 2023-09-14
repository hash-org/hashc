pub mod normalisation;

use hash_tir::{context::Context, sub::Sub, tir::NodeId};

use self::normalisation::NormalisationResult;
use crate::errors::TcResult;

pub trait Operations<X> {
    type TyNode: NodeId;
    type Node: NodeId;

    fn check(
        &self,
        ctx: &mut Context,
        item: &mut X,
        item_ty: Self::TyNode,
        item_node: Self::Node,
    ) -> TcResult<()>;

    fn normalise(
        &self,
        ctx: &mut Context,
        item: &mut X,
        item_node: Self::Node,
    ) -> NormalisationResult<()>;

    fn unify(
        &self,
        ctx: &mut Context,
        src: &mut X,
        target: &mut X,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()>;

    fn substitute(&self, sub: &Sub, target: &mut X) -> TcResult<()>;
}
