//! Traits for typechecking on TIR nodes.
//!
//! This defines a structured way to implement the typechecker, where
//! each node in the TIR `X` has a corresponding trait implementation
//! `Operations<X>` which defines how to typecheck, unify, and normalise that
//! node.
use std::ops::ControlFlow;

use crate::{diagnostics::TcResult, env::HasTcEnv, options::normalisation::NormaliseResult};

/// Main trait for typechecking on TIR atoms.
///
/// `X` is the TIR atom type.
pub trait OperationsOn<X>: HasTcEnv {
    /// The atom's annotation in the TIR.
    ///
    /// For example, if `X = MatchTerm`, `AnnotNode = TyId`.
    type AnnotNode;

    /// The actual TIR node that `X` is part of.
    ///
    /// For example, if `X = MatchTerm`, then `Node = TermId`.
    type Node;

    /// Check and infer the `item` in place (which might involve modification),
    /// with the annotation `item_ty` (which can also be modified), where `item`
    /// originates from `item_node`.
    fn check(&self, item: &mut X, item_ty: Self::AnnotNode, item_node: Self::Node) -> TcResult<()>;

    /// Normalise the given `item` if applicable, which originates from
    /// `item_node`.
    ///
    /// This returns a control flow result, where `Continue` means that the
    /// normalisation should just recurse to the children by TIR's
    /// `Visitor`.
    fn try_normalise(
        &self,
        item: X,
        item_node: Self::Node,
    ) -> NormaliseResult<ControlFlow<Self::Node>>;

    /// Unify the two atoms together in-place (which might involve
    /// modification), where `src` originates from `src_node` and `target`
    /// originates from `target_node`.
    fn unify(
        &self,
        src: &mut X,
        target: &mut X,
        src_node: Self::Node,
        target_node: Self::Node,
    ) -> TcResult<()>;
}

/// Simplification of `Operations` for the special case that `X = Self::Node`.
///
/// This is for TIR atoms which are node IDs themselves, where there would be no
/// difference between `item` and `item_node`.
pub trait OperationsOnNode<X: Copy>: HasTcEnv {
    /// The actual TIR node that `X` is part of.
    type AnnotNode;

    /// Check and infer the `item` in place (which might involve modification),
    /// with the annotation `item_ty` (which can also be modified).
    fn check_node(&self, item: X, item_ty: Self::AnnotNode) -> TcResult<()>;

    /// Normalise the given `item` if applicable.
    fn try_normalise_node(&self, item: X) -> NormaliseResult<ControlFlow<X>>;

    /// Unify the two nodes together in-place (which might involve
    /// modification).
    fn unify_nodes(&self, src: X, target: X) -> TcResult<()>;
}

/// Each `OperationsOnNode` is also an `OperationsOn`.
impl<X: Copy, T: HasTcEnv + OperationsOnNode<X>> OperationsOn<X> for T {
    type AnnotNode = T::AnnotNode;
    type Node = X;

    fn check(&self, item: &mut X, item_ty: Self::AnnotNode, _: Self::Node) -> TcResult<()> {
        self.check_node(*item, item_ty)
    }

    fn try_normalise(&self, item: X, _: Self::Node) -> NormaliseResult<ControlFlow<X>> {
        self.try_normalise_node(item)
    }

    fn unify(&self, src: &mut X, target: &mut X, _: Self::Node, _: Self::Node) -> TcResult<()> {
        self.unify_nodes(*src, *target)
    }
}

/// A version of `Operations` for nodes which have some inherent "context" to
/// them.
///
/// One example is `Params`, which adds the parameter names to the context. For
/// this reason, each TC operation here also receives a closure to run inside
/// the context created by the node.
pub trait ScopedOperationsOn<X>: HasTcEnv {
    /// The atom's annotation in the TIR.
    type AnnotNode;

    /// The actual TIR node that `X` is part of.
    type Node;

    /// What sort of argument to provide in the closure for callbacks.
    type CallbackArg;

    /// Check and infer the `item` in place (which might involve modification),
    /// with the annotation `item_ty` (which can also be modified), where `item`
    /// originates from `item_node`.
    ///
    /// This runs `f` in the context of the atom.
    fn check_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        item: &mut X,
        item_ty: Self::AnnotNode,
        item_node: Self::Node,
        f: F,
    ) -> TcResult<T>;

    /// Normalise the given `item` if applicable, which originates from
    /// `item_node`.
    ///
    /// Normalisation does not run in a scoped environment because generally
    /// scoped atoms are dealt with on a case-by-case basis.
    fn try_normalise(&self, item: X, item_node: Self::Node) -> NormaliseResult<ControlFlow<X>>;

    /// Unify the two atoms together in-place (which might involve
    /// modification), where `src` originates from `src_node` and `target`
    /// originates from `target_node`.
    ///
    /// This runs `f` in the context of the atom.
    fn unify_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        src: &mut X,
        target: &mut X,
        src_node: Self::Node,
        target_node: Self::Node,
        f: F,
    ) -> TcResult<T>;
}

/// Simplification of `ScopedOperations` for the special case that `X =
/// Self::Node`.
pub trait ScopedOperationsOnNode<X: Copy>: HasTcEnv {
    type AnnotNode;
    type CallbackArg;

    /// Check and infer the `item` in place (which might involve modification),
    /// with the annotation `item_ty`, running `f` in the context of the atom.
    fn check_node_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        item: X,
        item_ty: Self::AnnotNode,
        f: F,
    ) -> TcResult<T>;

    /// Normalise the given `item` if applicable, which originates from
    /// `item_node`.
    fn try_normalise_node(&self, item: X) -> NormaliseResult<ControlFlow<X>>;

    /// Unify the two nodes together in-place (which might involve
    /// modification), running `f` in the context of the atom.
    fn unify_nodes_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        src: X,
        target: X,
        f: F,
    ) -> TcResult<T>;
}

/// Each `ScopedOperationsOnNode` is also a `ScopedOperations`.
impl<X: Copy, U: ScopedOperationsOnNode<X> + HasTcEnv> ScopedOperationsOn<X> for U {
    type AnnotNode = U::AnnotNode;
    type Node = X;
    type CallbackArg = U::CallbackArg;

    fn check_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        item: &mut X,
        item_ty: Self::AnnotNode,
        _: Self::Node,
        f: F,
    ) -> TcResult<T> {
        self.check_node_scoped(*item, item_ty, f)
    }

    fn try_normalise(&self, item: X, _: Self::Node) -> NormaliseResult<ControlFlow<X>> {
        self.try_normalise_node(item)
    }

    fn unify_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        src: &mut X,
        target: &mut X,
        _: Self::Node,
        _: Self::Node,
        f: F,
    ) -> TcResult<T> {
        self.unify_nodes_scoped(*src, *target, f)
    }
}
