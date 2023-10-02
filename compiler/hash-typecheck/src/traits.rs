use crate::{env::HasTcEnv, errors::TcResult, options::normalisation::NormaliseResult};

pub trait Operations<X>: HasTcEnv {
    type TyNode;
    type Node;

    fn check(&self, item: &mut X, item_ty: Self::TyNode, item_node: Self::Node) -> TcResult<()>;

    fn try_normalise(&self, item: X, item_node: Self::Node) -> NormaliseResult<Self::Node>;

    fn unify(
        &self,
        src: &mut X,
        target: &mut X,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()>;
}

pub trait OperationsOnNode<X: Copy>: HasTcEnv {
    type TyNode;

    fn check_node(&self, item: X, item_ty: Self::TyNode) -> TcResult<()>;

    fn try_normalise_node(&self, item: X) -> NormaliseResult<X>;

    fn unify_nodes(&self, src: X, target: X) -> TcResult<()>;
}

impl<X: Copy, T: HasTcEnv + OperationsOnNode<X>> Operations<X> for T {
    type TyNode = T::TyNode;
    type Node = X;

    fn check(&self, item: &mut X, item_ty: Self::TyNode, _: Self::Node) -> TcResult<()> {
        self.check_node(*item, item_ty)
    }

    fn try_normalise(&self, item: X, _: Self::Node) -> NormaliseResult<X> {
        self.try_normalise_node(item)
    }

    fn unify(&self, src: &mut X, target: &mut X, _: Self::Node, _: Self::Node) -> TcResult<()> {
        self.unify_nodes(*src, *target)
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

    fn try_normalise(&self, item: X, item_node: Self::Node) -> NormaliseResult<X>;

    fn unify_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        src: &mut X,
        target: &mut X,
        src_node: Self::Node,
        target_node: Self::Node,
        f: F,
    ) -> TcResult<T>;
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

    fn try_normalise_node_rec(&self, item: X) -> NormaliseResult<X>;

    fn unify_nodes_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        src: X,
        target: X,
        f: F,
    ) -> TcResult<T>;
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

    fn try_normalise(&self, item: X, _: Self::Node) -> NormaliseResult<X> {
        self.try_normalise_node_rec(item)
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
}
