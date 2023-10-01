pub mod normalisation;
pub mod unification;

use hash_tir::sub::Sub;

use self::normalisation::NormaliseResult;
use crate::{env::HasTcEnv, errors::TcResult};

pub trait Operations<X>: HasTcEnv {
    type TyNode;
    type Node;

    fn check(&self, item: &mut X, item_ty: Self::TyNode, item_node: Self::Node) -> TcResult<()>;

    fn normalise(&self, item: X, item_node: Self::Node) -> NormaliseResult<Self::Node>;

    fn unify(
        &self,
        src: &mut X,
        target: &mut X,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()>;

    fn substitute(&self, sub: &Sub, target: &mut X);
}

pub trait OperationsOnNode<X: Copy>: HasTcEnv {
    type TyNode;

    fn check_node(&self, item: X, item_ty: Self::TyNode) -> TcResult<()>;

    fn normalise_node(&self, item: X) -> NormaliseResult<X>;

    fn unify_nodes(&self, src: X, target: X) -> TcResult<()>;

    fn substitute_node(&self, sub: &Sub, target: X);
}

impl<X: Copy, T: HasTcEnv + OperationsOnNode<X>> Operations<X> for T {
    type TyNode = T::TyNode;
    type Node = X;

    fn check(&self, item: &mut X, item_ty: Self::TyNode, _: Self::Node) -> TcResult<()> {
        self.check_node(*item, item_ty)
    }

    fn normalise(&self, item: X, _: Self::Node) -> NormaliseResult<X> {
        self.normalise_node(item)
    }

    fn unify(&self, src: &mut X, target: &mut X, _: Self::Node, _: Self::Node) -> TcResult<()> {
        self.unify_nodes(*src, *target)
    }

    fn substitute(&self, sub: &Sub, target: &mut X) {
        self.substitute_node(sub, *target)
    }
}

pub trait RecursiveOperations<X>: HasTcEnv {
    type TyNode;
    type Node;
    type RecursiveArg;

    fn check_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        item: &mut X,
        item_ty: Self::TyNode,
        item_node: Self::Node,
        f: F,
    ) -> TcResult<T>;

    fn normalise(&self, item: X, item_node: Self::Node) -> NormaliseResult<X>;

    #[allow(clippy::too_many_arguments)]
    fn unify_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        src: &mut X,
        target: &mut X,
        src_node: Self::Node,
        target_node: Self::Node,
        f: F,
    ) -> TcResult<T>;

    fn substitute_rec<T, F: FnMut(Self::RecursiveArg) -> T>(
        &self,
        sub: &Sub,
        target: &mut X,
        f: F,
    ) -> T;
}

pub trait RecursiveOperationsOnNode<X: Copy>: HasTcEnv {
    type TyNode;
    type RecursiveArg;

    fn check_node_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        item: X,
        item_ty: Self::TyNode,
        f: F,
    ) -> TcResult<T>;

    fn normalise_node(&self, item: X) -> NormaliseResult<X>;

    fn unify_nodes_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        src: X,
        target: X,
        f: F,
    ) -> TcResult<T>;

    fn substitute_node_rec<T, F: FnMut(Self::RecursiveArg) -> T>(
        &self,
        sub: &Sub,
        target: X,
        f: F,
    ) -> T;
}

impl<X: Copy, U: RecursiveOperationsOnNode<X> + HasTcEnv> RecursiveOperations<X> for U {
    type TyNode = U::TyNode;
    type Node = X;
    type RecursiveArg = U::RecursiveArg;

    fn check_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        item: &mut X,
        item_ty: Self::TyNode,
        _: Self::Node,
        f: F,
    ) -> TcResult<T> {
        self.check_node_rec(*item, item_ty, f)
    }

    fn normalise(&self, item: X, _: Self::Node) -> NormaliseResult<X> {
        self.normalise_node(item)
    }

    fn unify_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        src: &mut X,
        target: &mut X,
        _: Self::Node,
        _: Self::Node,
        f: F,
    ) -> TcResult<T> {
        self.unify_nodes_rec(*src, *target, f)
    }

    fn substitute_rec<T, F: FnMut(Self::RecursiveArg) -> T>(
        &self,
        sub: &Sub,
        target: &mut X,
        f: F,
    ) -> T {
        self.substitute_node_rec(sub, *target, f)
    }
}
