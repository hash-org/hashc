pub mod checking;
pub mod normalisation;
pub mod unification;

use hash_tir::{context::Context, sub::Sub, tir::NodeId};

use self::{checking::CheckResult, normalisation::NormaliseResult};
use crate::{env::HasTcEnv, errors::TcResult};

pub trait Operations<X>: HasTcEnv {
    type TyNode: NodeId;
    type Node: NodeId;

    fn check(
        &self,
        ctx: &mut Context,
        item: &mut X,
        item_ty: Self::TyNode,
        item_node: Self::Node,
    ) -> CheckResult;

    fn normalise(
        &self,
        ctx: &mut Context,
        item: &mut X,
        item_node: Self::Node,
    ) -> NormaliseResult<()>;

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
