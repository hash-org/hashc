//! This module defines a post order traversal of a graph with a given root
//! node. Post order traversal is a depth first traversal of a graph where all
//! of the children of a node are visited before the node itself.

use fixedbitset::FixedBitSet;
use index_vec::{index_vec, Idx};

use super::{DirectedGraph, WithSuccessors};

/// A post order traversal of a graph with a given root node.
pub fn post_order_from_to<G: DirectedGraph + WithSuccessors>(
    graph: &G,
    start_node: G::Node,
    end_node: Option<G::Node>,
) -> Vec<G::Node> {
    let mut visited = index_vec![false; graph.num_nodes()];
    let mut stack = vec![start_node];
    let mut post_order = vec![];

    // If an end-node is given, we mark the end node as being
    // visited.
    if let Some(end_node) = end_node {
        visited[end_node] = true;
    }

    while let Some(node) = stack.pop() {
        if visited[node] {
            continue;
        }

        visited[node] = true;

        if end_node.map_or(true, |end_node| node != end_node) {
            stack.push(node);
            for successor in graph.successors(node) {
                stack.push(successor);
            }
        } else {
            post_order.push(node);
        }
    }

    post_order
}

/// A "depth-first search" iterator for a directed graph.
pub struct DepthFirstSearch<'graph, G>
where
    G: ?Sized + DirectedGraph + WithSuccessors,
{
    /// The graph that we are traversing.
    graph: &'graph G,

    /// A stack of nodes that we have yet to visit.
    stack: Vec<G::Node>,

    /// A set of nodes that have been visited.
    visited: FixedBitSet,
}

impl<'graph, G: ?Sized + DirectedGraph + WithSuccessors> DepthFirstSearch<'graph, G> {
    /// Create a new depth-first search iterator for the given graph.
    pub fn new(graph: &'graph G, start_node: G::Node) -> Self {
        let mut visited = FixedBitSet::with_capacity(graph.num_nodes());

        // we need to insert the starting node, and push it onto the stack
        visited.insert(start_node.index());

        Self { graph, stack: vec![start_node], visited }
    }

    /// Check if a node has been visited yet.
    pub fn visited(&self, node: G::Node) -> bool {
        self.visited.contains(node.index())
    }
}

impl<G> Iterator for DepthFirstSearch<'_, G>
where
    G: ?Sized + DirectedGraph + WithSuccessors,
{
    type Item = G::Node;

    fn next(&mut self) -> Option<Self::Item> {
        let DepthFirstSearch { stack, visited, graph } = self;
        let n = stack.pop()?;

        // Add all of the successors of the graph that haven't
        // been visited yet.
        stack.extend(graph.successors(n).filter(|&m| {
            if visited.contains(m.index()) {
                false
            } else {
                visited.insert(m.index());
                true
            }
        }));

        Some(n)
    }
}
