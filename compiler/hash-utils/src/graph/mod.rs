//! This module contains graph algorithms and utilities that are used by the
//! compiler.

pub mod dominators;
pub mod visit;

use index_vec::Idx;

/// This trait can be used to represent a generic directed
/// graph. The index of each graph node used a [`index_vec::Idx`].
pub trait DirectedGraph {
    type Node: Idx;

    /// Compute the number of nodes in the whole graph.
    fn num_nodes(&self) -> usize;
}

pub trait GraphPredecessors<'graph> {
    type Item;
    type Iter: Iterator<Item = Self::Item> + 'graph;
}

/// A trait that is used to denote that a [`DirectedGraph`] can
/// be used to compute the predecessors of a node.
pub trait WithPredecessors: DirectedGraph
where
    Self: for<'graph> GraphPredecessors<'graph, Item = <Self as DirectedGraph>::Node>,
{
    fn predecessors(&self, node: Self::Node) -> <Self as GraphPredecessors>::Iter;
}

pub trait GraphSuccessors<'graph> {
    type Item;
    type Iter: Iterator<Item = Self::Item> + 'graph;
}

/// A trait that is used to denote that a [`DirectedGraph`] can
/// be used to compute the successors of a node.
pub trait WithSuccessors: DirectedGraph
where
    Self: for<'graph> GraphSuccessors<'graph, Item = <Self as DirectedGraph>::Node>,
{
    /// Get the successors of a node.
    fn successors(&self, node: Self::Node) -> <Self as GraphSuccessors>::Iter;

    /// Create a [DepthFirstSearch] iterator that starts at the given
    /// node.
    fn depth_first_search(&self, from: Self::Node) -> visit::DepthFirstSearch<'_, Self> {
        visit::DepthFirstSearch::new(self, from)
    }
}

/// A trait that describes all of the properties that a control flow
/// graph should have. This is mostly a convenience trait that is used
/// to denote that a graph has both predecessors and successors.
pub trait ControlFlowGraph: DirectedGraph + WithPredecessors + WithSuccessors {
    /// Return the start node of the graph which all [ControlFlowGraph]s
    /// have.
    ///
    /// N.B. The default implementation of this method assumes that the
    /// start node is always `0`.
    fn start_node(&self) -> Self::Node {
        Self::Node::from_usize(0)
    }
}

impl<T> ControlFlowGraph for T where T: DirectedGraph + WithPredecessors + WithSuccessors {}
