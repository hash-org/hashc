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
pub struct DepthFirstTraversal<'graph, G>
where
    G: ?Sized + DirectedGraph + WithSuccessors,
{
    /// The graph that we are traversing.
    graph: &'graph G,

    /// A stack of nodes that we have yet to visit.
    stack: Vec<G::Node>,

    /// A set of nodes that have been visited.
    discovered: FixedBitSet,

    /// A set of nodes that have been visited.
    visited: FixedBitSet,
}

impl<'graph, G: ?Sized + DirectedGraph + WithSuccessors> DepthFirstTraversal<'graph, G> {
    /// Create a new depth-first search iterator for the given graph.
    pub fn new(graph: &'graph G, start_node: G::Node) -> Self {
        let visited = FixedBitSet::with_capacity(graph.num_nodes());
        let discovered = FixedBitSet::with_capacity(graph.num_nodes());

        Self { graph, stack: vec![start_node], visited, discovered }
    }
}

impl<G> Iterator for DepthFirstTraversal<'_, G>
where
    G: ?Sized + DirectedGraph + WithSuccessors,
{
    type Item = G::Node;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(&node) = self.stack.last() {
            if !self.discovered.put(node.index()) {
                // First time visiting `nx`: Push neighbors, don't pop `nx`
                for successor in self.graph.successors(node) {
                    if !self.discovered.contains(successor.index()) {
                        self.stack.push(successor);
                    }
                }
            } else {
                self.stack.pop();

                if !self.visited.put(node.index()) {
                    // Second time: All reachable nodes must have been finished
                    return Some(node);
                }
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // We will visit every node in the graph exactly once.
        let remaining = self.graph.num_nodes() - self.visited.count_ones(..);
        (remaining, Some(remaining))
    }
}

#[cfg(test)]
mod test_super {
    use crate::graph::{
        tests::{TestGraph, TestNode},
        visit::DepthFirstTraversal,
    };

    #[test]
    fn test_post_order_traversal() {
        let graph = TestGraph::new(0, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
        let post_order = DepthFirstTraversal::new(&graph, TestNode::new(0));

        let expected_order =
            vec![TestNode::new(3), TestNode::new(2), TestNode::new(1), TestNode::new(0)];

        assert_eq!(post_order.collect::<Vec<_>>(), expected_order);
    }
}
