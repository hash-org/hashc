//! Defines the type wrapper for TIR nodes, which contains some
//! metadata about the node, and the data itself.
//!
//! The metadata includes the node origin, which points to the
//! AST node that the TIR node was generated from, if any.
//!
//! Nodes normally live in stores, which can be created through the
//! `crate::environment::stores::tir_node_*` macros.
use core::fmt;

use hash_ast::ast::AstNodeId;
use hash_source::{location::Span, SourceId};
use hash_storage::store::statics::{SequenceStoreId, SingleStoreValue};
use hash_utils::derive_more::{Deref, DerefMut};

/// A trait used to access AST information about a particular
/// type. This is useful for when we want to access the [AstNodeId]
/// of a particular node.
pub trait HasAstNodeId {
    /// Get the [AstNodeId] of the node.
    fn node_id(&self) -> Option<AstNodeId>;

    /// Get the [AstNodeId] of the node, or panic if it does not exist.
    fn node_id_ensured(&self) -> AstNodeId {
        self.node_id().expect("Expected node id to exist")
    }

    /// Get the [AstNodeId] or default to a [`AstNodeId::null()`].
    fn node_id_or_default(&self) -> AstNodeId {
        self.node_id().unwrap_or_else(AstNodeId::null)
    }

    /// Get the span of this node.
    fn span(&self) -> Option<Span> {
        self.node_id().map(|n| n.span())
    }

    /// Get the source ID of this node.
    fn source(&self) -> Option<SourceId> {
        self.node_id().map(|n| n.source())
    }
}

impl<T: HasAstNodeId> HasAstNodeId for &T {
    fn node_id(&self) -> Option<AstNodeId> {
        (*self).node_id()
    }
}

/// A trait implemented by all TIR node IDs.
pub trait NodeId: HasAstNodeId {
    /// Get the origin of the TIR node.
    fn origin(self) -> NodeOrigin;
}

/// A trait implemented by all TIR sequence store node ID wrappers.
///
/// See `crate::environment::stores::tir_node_*_sequence_store` for more
/// information.
pub trait NodesId: NodeId {
    type Elements: SequenceStoreId;

    /// Get the underlying sequence node of the TIR node.
    fn elements_node(&self) -> Node<Self::Elements>;

    /// Get the elements of the TIR node.
    fn elements(&self) -> Self::Elements {
        self.elements_node().data
    }
}

/// Represents a node in the TIR.
///
/// Each node has an origin, and data associated with it.
#[derive(Debug, Deref, DerefMut, Copy, Clone, PartialEq, Eq)]
pub struct Node<Data> {
    pub origin: NodeOrigin,
    #[deref]
    #[deref_mut]
    pub data: Data,
}

/// Helper implementation for `Node`s which are also `SingleStoreValue`s,
/// so that a node and its entry in the store can be created in one go.
impl<Data> Node<Data>
where
    Self: SingleStoreValue,
{
    /// Create a new node with the given data and origin, and insert it into the
    /// store.
    pub fn create_at(data: Data, origin: NodeOrigin) -> <Self as SingleStoreValue>::Id {
        Self::create(Self::at(data, origin))
    }

    /// Create a new node with the given data and a generated origin, and insert
    /// it into the store.
    pub fn create_gen(data: Data) -> <Self as SingleStoreValue>::Id {
        Self::create(Self::gen(data))
    }
}

impl<Data> Node<Data> {
    /// Create a new node with the given data and origin.
    pub fn at(data: Data, origin: NodeOrigin) -> Self {
        Self { data, origin }
    }

    /// Create a new node with the given data and a generated origin.
    pub fn gen(data: Data) -> Self {
        Self { data, origin: NodeOrigin::Generated }
    }

    /// Get the node ID of this node.
    pub fn node(&self) -> Option<AstNodeId> {
        self.origin.node()
    }

    /// Create a new node with the same origin, but different data.
    pub fn with_data<E>(&self, new_data: E) -> Node<E> {
        Node { data: new_data, origin: self.origin }
    }
}

/// A tuple of data and origin can be converted into a node.
impl<D, Data: From<D>> From<(D, NodeOrigin)> for Node<Data> {
    fn from((d, o): (D, NodeOrigin)) -> Self {
        Node::at(d.into(), o)
    }
}

impl<T> HasAstNodeId for Node<T> {
    fn node_id(&self) -> Option<AstNodeId> {
        self.origin.node_id()
    }
}

impl HasAstNodeId for NodeOrigin {
    fn node_id(&self) -> Option<AstNodeId> {
        match self {
            NodeOrigin::ComputedFrom(id) | NodeOrigin::Given(id) | NodeOrigin::InferredFrom(id) => {
                Some(*id)
            }
            NodeOrigin::Expected | NodeOrigin::Generated => None,
        }
    }
}

impl<T: fmt::Display> fmt::Display for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data.fmt(f)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum NodeOrigin {
    /// The node was given by the user.
    Given(AstNodeId),
    /// The node was created through type inference of the given origin.
    InferredFrom(AstNodeId),
    /// The node was computed through compile-time evaluation of the given
    /// origin.
    ComputedFrom(AstNodeId),
    /// The node was created during type checking because it is expected to
    /// match a user-given type. For example, the `bool` type node created for
    /// unification in `IfPat` patterns will have a
    /// `NodeOrigin::Expected`.
    Expected,
    /// The node was generated by the compiler, and has no origin.
    ///
    /// When this variant is used, the surrounding code should be annotated with
    /// a `##GeneratedOrigin` comment justifying the lack of origin.
    Generated,
}

impl NodeOrigin {
    /// Get the node ID of this origin, if any.
    pub fn node(&self) -> Option<AstNodeId> {
        match self {
            NodeOrigin::ComputedFrom(node)
            | NodeOrigin::Given(node)
            | NodeOrigin::InferredFrom(node) => Some(*node),
            NodeOrigin::Expected | NodeOrigin::Generated => None,
        }
    }

    /// Create a new origin which is inferred from the current one.
    pub fn inferred(&self) -> Self {
        match self {
            NodeOrigin::ComputedFrom(g) | NodeOrigin::Given(g) | NodeOrigin::InferredFrom(g) => {
                NodeOrigin::InferredFrom(*g)
            }
            NodeOrigin::Expected | NodeOrigin::Generated => *self,
        }
    }

    /// Create a new origin which is computed from the current one.
    pub fn computed(&self) -> Self {
        match self {
            NodeOrigin::ComputedFrom(g) | NodeOrigin::Given(g) | NodeOrigin::InferredFrom(g) => {
                NodeOrigin::ComputedFrom(*g)
            }
            NodeOrigin::Expected | NodeOrigin::Generated => *self,
        }
    }

    /// Create a node with this origin and the given data.
    pub fn with_data<E>(&self, data: E) -> Node<E> {
        Node { data, origin: *self }
    }
}
