//! This module implements an algorithm to find all of the
//! dominators of a given control flow graph. A "dominator" of a node
//! is a vertex node that lies on all paths from the root vertex
//! node (i.e. in a control flow graph, `bb0` block).
//!
//! This module implements the algorithm described in the paper
//! "A Simple, Fast Dominance Algorithm" by Keith D. Cooper, Timothy J. Harvey.

use std::{cmp::Ordering, collections::HashSet};

use index_vec::{index_vec, Idx, IndexVec};

use super::ControlFlowGraph;

/// The [Dominators] of a control flow graph. This is a mapping from
/// each node in the graph to its dominator, and has an associated `root`
/// node which is the root of the graph.
pub struct Dominators<Node: Idx> {
    /// The root node of the graph.
    root: Node,

    /// The dominators of each node in the graph.
    dominators: IndexVec<Node, Node>,
}

impl<Node: Idx> Dominators<Node> {
    /// Compute the dominators of a given control flow graph. This implements
    /// the algorithm described in the paper "A Simple, Fast Dominance
    /// Algorithm" by Keith D. Cooper, Timothy J. Harvey. The reference
    /// paper is available at: https://www.cs.rice.edu/~keith/EMBED/dom.pdf
    pub fn new<G: ControlFlowGraph<Node = Node>>(graph: &G) -> Self {
        let root = graph.start_node();
        let (post_order, predecessor_sets) = post_order_with_predecessors(graph);
        let length = post_order.len();

        debug_assert!(length > 0);
        debug_assert!(post_order.last() == Some(&graph.start_node()));

        let empty_marker = G::Node::from_usize(usize::MAX);
        let mut dominators = index_vec![empty_marker; length];

        // set the dominator of the root node to be itself
        dominators[root] = root;

        let mut changed = true;

        while changed {
            changed = false;

            // Iterate in reverse post-order
            for idx in (0..length - 1).rev() {
                debug_assert!(post_order[idx] != root);

                // Take the intersection of every predecessor's dominator set; that
                // is the current best guess at the immediate dominator for this
                // node.

                let new_idom_idx = {
                    let mut predecessors = predecessor_sets[idx]
                        .iter()
                        .filter(|&predecessor| dominators[*predecessor] != empty_marker);

                    // get the first index in the predecessors
                    let new_dom_idx = predecessors.next().unwrap();

                    predecessors.fold(*new_dom_idx, |mut new_dom_idx, mut predecessor_idx| loop {
                        match new_dom_idx.cmp(predecessor_idx) {
                            Ordering::Less => new_dom_idx = dominators[new_dom_idx],
                            Ordering::Greater => predecessor_idx = &dominators[*predecessor_idx],
                            Ordering::Equal => return new_dom_idx,
                        }
                    })
                };

                debug_assert!(new_idom_idx.index() < length);

                if new_idom_idx != dominators[idx] {
                    dominators[idx] = new_idom_idx;
                    changed = true;
                }
            }
        }

        Self { root: graph.start_node(), dominators }
    }

    /// Get the immediate dominator of a particular node.
    pub fn immediate_dominator(&self, node: Node) -> Node {
        debug_assert!(self.dominators[node] != self.root);
        self.dominators[node]
    }
}

pub struct DominatorsIter<'dom, Node: Idx> {
    /// The computed dominators of a graph.
    dominators: &'dom Dominators<Node>,

    ///
    node: Option<Node>,
}

impl<'dom, Node: Idx> Iterator for DominatorsIter<'dom, Node> {
    type Item = Node;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.node {
            let dom = self.dominators.immediate_dominator(node);

            if dom == node {
                self.node = None; // reached the root
            } else {
                self.node = Some(dom);
            }
            Some(node)
        } else {
            None
        }
    }
}

type PredecessorSets<Node> = IndexVec<Node, HashSet<Node>>;

/// Compute the post-order traversal of a graph, along with the
/// predecessor sets for each node.
fn post_order_with_predecessors<G: ControlFlowGraph>(
    graph: &G,
) -> (Vec<G::Node>, PredecessorSets<G::Node>) {
    let mut post_order = vec![];
    let mut predecessor_sets = index_vec![HashSet::new(); graph.num_nodes()];

    for node in graph.depth_first_search(graph.start_node()) {
        post_order.push(node);
        for successor in graph.successors(node) {
            predecessor_sets[successor].insert(node);
        }
    }

    (post_order, predecessor_sets)
}
