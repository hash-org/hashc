pub mod checking;
pub mod normalisation;
pub mod unification;

use hash_tir::{
    context::Context,
    sub::Sub,
    visitor::{Map, Visit, Visitor},
};

use self::{checking::CheckResult, normalisation::NormaliseResult, unification::UnifyResult};
use crate::env::HasTcEnv;

pub trait Operations<X>: HasTcEnv {
    type TyNode;
    type Node;

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
    ) -> UnifyResult;

    fn substitute(&self, sub: &Sub, target: &mut X);
}

pub trait OperationsOnNode<X: Copy>: Operations<X, Node = X>
where
    Visitor: Visit<X> + Map<X>,
{
    fn check_node(&self, ctx: &mut Context, item: X, item_ty: Self::TyNode) -> CheckResult {
        let mut item_ref = item;
        Operations::check(self, ctx, &mut item_ref, item_ty, item)
    }

    fn normalise_node(&self, ctx: &mut Context, item: X) -> NormaliseResult<()> {
        let mut item_ref = item;
        Operations::normalise(self, ctx, &mut item_ref, item)
    }

    fn unify_nodes(&self, ctx: &mut Context, src: X, target: X) -> UnifyResult {
        let mut src_ref = src;
        let mut target_ref = target;
        Operations::unify(self, ctx, &mut src_ref, &mut target_ref, src, target)
    }

    fn substitute_in_node(&self, sub: &Sub, mut target: X) {
        Operations::substitute(self, sub, &mut target)
    }

    fn copy_node(&self, target: X) -> X {
        Visitor::new().copy(target)
    }

    fn substitute_in_node_copied(&self, sub: &Sub, target: X) -> X {
        let mut copied = self.copy_node(target);
        Operations::substitute(self, sub, &mut copied);
        copied
    }
}

impl<X: Copy, T: Operations<X, Node = X>> OperationsOnNode<X> for T where Visitor: Visit<X> + Map<X> {}

pub trait RecursiveOperations<X>: HasTcEnv {
    type TyNode;
    type Node;

    fn check<T, F: FnMut() -> CheckResult<T>>(
        &self,
        ctx: &mut Context,
        item: &mut X,
        item_ty: Self::TyNode,
        item_node: Self::Node,
        f: F,
    ) -> CheckResult<T>;

    fn normalise<T, F: FnMut() -> NormaliseResult<T>>(
        &self,
        ctx: &mut Context,
        item: &mut X,
        item_node: Self::Node,
        f: F,
    ) -> NormaliseResult<T>;

    fn unify<T, F: FnMut() -> UnifyResult<T>>(
        &self,
        ctx: &mut Context,
        src: &mut X,
        target: &mut X,
        src_node: Self::Node,
        target_node: Self::Node,
        f: F,
    ) -> UnifyResult<T>;

    fn substitute<T, F: FnMut() -> T>(&self, sub: &Sub, target: &mut X, f: F) -> T;
}

pub trait RecursiveOperationsOnNode<X: Copy>: RecursiveOperations<X, Node = X>
where
    Visitor: Visit<X> + Map<X>,
{
    fn check_node<T, F: FnMut() -> CheckResult<T>>(
        &self,
        ctx: &mut Context,
        item: X,
        item_ty: Self::TyNode,
        f: F,
    ) -> CheckResult<T> {
        let mut item_ref = item;
        RecursiveOperations::check(self, ctx, &mut item_ref, item_ty, item, f)
    }

    fn normalise_node<T, F: FnMut() -> NormaliseResult<T>>(
        &self,
        ctx: &mut Context,
        item: X,
        f: F,
    ) -> NormaliseResult<T> {
        let mut item_ref = item;
        RecursiveOperations::normalise(self, ctx, &mut item_ref, item, f)
    }

    fn unify_nodes<T, F: FnMut() -> UnifyResult<T>>(
        &self,
        ctx: &mut Context,
        src: X,
        target: X,
        f: F,
    ) -> UnifyResult<T> {
        let mut src_ref = src;
        let mut target_ref = target;
        RecursiveOperations::unify(self, ctx, &mut src_ref, &mut target_ref, src, target, f)
    }

    fn substitute_in_node<T, F: FnMut() -> T>(&self, sub: &Sub, mut target: X, f: F) -> T {
        RecursiveOperations::substitute(self, sub, &mut target, f)
    }

    fn copy_node(&self, target: X) -> X {
        Visitor::new().copy(target)
    }

    fn substitute_in_node_copied<T, F: FnMut()>(&self, sub: &Sub, target: X, f: F) -> X {
        let mut copied = self.copy_node(target);
        RecursiveOperations::substitute(self, sub, &mut copied, f);
        copied
    }
}

impl<X: Copy, T: RecursiveOperations<X, Node = X>> RecursiveOperationsOnNode<X> for T where
    Visitor: Visit<X> + Map<X>
{
}
