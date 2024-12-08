//! This module implements an algorithm to find all of the
//! dominators of a given control flow graph. A "dominator" of a node
//! is a vertex node that lies on all paths from the root vertex
//! node (i.e. in a control flow graph, `bb0` block).
//!
//! This module implements the algorithm described in the paper:
//!
//! "A Fast Algorithm for Finding Dominators in a Flowgraph"
//! Thomas Lengauer and Robert Endre Tarjan.
//! <https://www.cs.princeton.edu/courses/archive/spr03/cs423/download/dominators.pdf>

use std::cmp::Ordering;

use index_vec::{define_index_type, index_vec, Idx, IndexVec};
use smallvec::{smallvec, SmallVec};

use super::ControlFlowGraph;

/// The [Dominators] of a control flow graph. This is a mapping from
/// each node in the graph to its dominator, and has an associated `root`
/// node which is the root of the graph.
pub struct Dominators<Node: Idx> {
    post_order_rank: IndexVec<Node, usize>,

    /// The dominators of each node in the graph.
    immediate_dominators: IndexVec<Node, Option<Node>>,
}

impl<Node: Idx> Dominators<Node> {
    pub fn dummy() -> Self {
        Self { post_order_rank: IndexVec::new(), immediate_dominators: IndexVec::new() }
    }

    /// Check if a node is reachable from the root node.
    pub fn is_reachable(&self, node: Node) -> bool {
        self.immediate_dominators[node].is_some()
    }

    /// Get the immediate dominator of a particular node.
    pub fn immediate_dominator(&self, node: Node) -> Node {
        debug_assert!(self.is_reachable(node), "node `{node:?}` is not reachable");
        self.immediate_dominators[node].unwrap()
    }

    /// Get all of the dominators of a particular node.
    pub fn dominators(&self, node: Node) -> DominatorsIter<'_, Node> {
        DominatorsIter { dominators: self, node: Some(node) }
    }

    /// Check if a particular node is a dominator of another node.
    pub fn is_dominated_by(&self, node: Node, dominator: Node) -> bool {
        self.dominators(node).any(|node_dominator| node_dominator == dominator)
    }

    /// Provide deterministic ordering of nodes such that, if any two nodes have
    /// a dominator relationship, the dominator will always precede the
    /// dominated. (The relative ordering of two unrelated nodes will also
    /// be consistent, but otherwise the order has no meaning.)
    ///
    /// N.B. This method cannot be used to determine if either `Node` dominates
    /// the other.
    pub fn rank_partial_cmp(&self, lhs: Node, rhs: Node) -> Option<Ordering> {
        self.post_order_rank[lhs].partial_cmp(&self.post_order_rank[rhs])
    }
}

/// An iterator over the dominators of a particular node.
pub struct DominatorsIter<'dom, Node: Idx> {
    /// The computed dominators of a graph.
    dominators: &'dom Dominators<Node>,

    /// The node to find dominators against. Whilst the iterator is
    /// active, this will be set to the current dominator.
    node: Option<Node>,
}

impl<Node: Idx> Iterator for DominatorsIter<'_, Node> {
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

define_index_type! {
    /// A pre-order index into a graph.
    struct PreOrderIndex = u32;
}

/// A frame in the pre-order traversal of a graph.
struct PreOrderFrame<Iter> {
    /// The pre-order index of the current node.
    pre_order_index: PreOrderIndex,

    /// The iterator over the successors of the current node.
    iter: Iter,
}

/// Create an `IndexVec` with `n` elements, where the value of each
/// element is the result of `func(i)`. (The underlying vector will
/// be allocated only once, with a capacity of at least `n`.)
///
/// @@Todo: move this into index vec extensions...
#[inline]
fn from_fn_n<I: Idx, T>(func: impl FnMut(I) -> T, n: usize) -> IndexVec<I, T> {
    let indices = (0..n).map(I::from_usize);
    IndexVec::from_vec(indices.map(func).collect())
}

fn is_processed(node: PreOrderIndex, last_linked: Option<PreOrderIndex>) -> bool {
    last_linked.is_some_and(|last_linked| node >= last_linked)
}

fn compress(
    ancestor: &mut IndexVec<PreOrderIndex, PreOrderIndex>,
    last_linked: Option<PreOrderIndex>,
    semi: &IndexVec<PreOrderIndex, PreOrderIndex>,
    label: &mut IndexVec<PreOrderIndex, PreOrderIndex>,
    node: PreOrderIndex,
) {
    debug_assert!(is_processed(node, last_linked));

    let mut stack: SmallVec<[_; 8]> = smallvec![node];
    let mut u = ancestor[node];

    while is_processed(u, last_linked) {
        stack.push(u);
        u = ancestor[u];
    }

    // Then in reverse order, pop the stack
    for &[v, u] in stack.array_windows().rev() {
        if semi[label[u]] < semi[label[v]] {
            label[v] = label[u];
        }

        ancestor[v] = ancestor[u];
    }
}

/// Evaluate the link-eval virtual forest, providing the currently minimum semi
/// value for the passed `node`, which could be itself.
///
/// This maintains that for every vertex `v`, `label[v]` is such that:
/// ```text
/// semi[eval(v)] = min { semi[w] | root_in_forest(v) +> u *v }
/// ```
/// where `+>` is a proper ancestor and `*>` is just an ancestor.
fn eval(
    ancestor: &mut IndexVec<PreOrderIndex, PreOrderIndex>,
    last_linked: Option<PreOrderIndex>,
    semi: &IndexVec<PreOrderIndex, PreOrderIndex>,
    label: &mut IndexVec<PreOrderIndex, PreOrderIndex>,
    node: PreOrderIndex,
) -> PreOrderIndex {
    if is_processed(node, last_linked) {
        compress(ancestor, last_linked, semi, label, node);
        label[node]
    } else {
        node
    }
}

/// This function computes the dominators of a graph using the Lengauer-Tarjan
/// [algorithm][<https://www.cs.princeton.edu/courses/archive/spr03/cs423/download/dominators.pdf>].
///
/// This implements the pseudo-code from this paper, and is based on the
/// Rust compiler implementation of the algorithm.
pub fn dominators<G: ControlFlowGraph>(graph: &G) -> Dominators<G::Node> {
    let mut post_order_rank = index_vec![0; graph.num_nodes()];

    let mut parent: IndexVec<PreOrderIndex, PreOrderIndex> =
        IndexVec::with_capacity(graph.num_nodes());

    let mut stack = vec![PreOrderFrame {
        pre_order_index: PreOrderIndex::new(0),
        iter: graph.successors(graph.start_node()),
    }];

    // We store a mapping of pre-order indexes to the actual graph indexes, and
    // backwards
    let mut pre_order_to_real: IndexVec<PreOrderIndex, G::Node> =
        IndexVec::with_capacity(graph.num_nodes());
    let mut real_to_pre_order: IndexVec<G::Node, Option<PreOrderIndex>> =
        index_vec![None; graph.num_nodes()];

    pre_order_to_real.push(graph.start_node());
    parent.push(PreOrderIndex::new(0));
    real_to_pre_order[graph.start_node()] = Some(PreOrderIndex::new(0));
    let mut post_order_index = 0;

    // Traverse the graph in pre-order, and build up the following information:
    //
    // 1. pre-order to real mapping - `pre_order_to_real`
    //
    // 2. post-ordering mapping, which will be used for `rank_partial_cmp` -
    // `post_order_rank`
    //
    // 3. parents for each graph vertex - `parent`
    'recurse: while let Some(frame) = stack.last_mut() {
        for successor in frame.iter.by_ref() {
            if real_to_pre_order[successor].is_none() {
                let pre_order_index = pre_order_to_real.push(successor);
                real_to_pre_order[successor] = Some(pre_order_index);

                parent.push(frame.pre_order_index);
                stack.push(PreOrderFrame { pre_order_index, iter: graph.successors(successor) });
                continue 'recurse;
            }
        }

        post_order_rank[pre_order_to_real[frame.pre_order_index]] = post_order_index;
        post_order_index += 1;
        stack.pop();
    }

    let reachable_vertices = pre_order_to_real.len();

    let mut idom: IndexVec<PreOrderIndex, PreOrderIndex> =
        index_vec![PreOrderIndex::new(0); reachable_vertices];

    let mut semi = from_fn_n(std::convert::identity, reachable_vertices);
    let mut label = semi.clone();

    let mut bucket = index_vec![vec![]; reachable_vertices];
    let mut last_linked = None;

    for w in (1..reachable_vertices).rev() {
        let w = PreOrderIndex::new(w);
        let z = parent[w];

        for &v in bucket[z].iter() {
            let y = eval(&mut parent, last_linked, &semi, &mut label, v);
            idom[v] = if semi[y] < z { y } else { z };
        }

        semi[w] = w;
        for v in graph.predecessors(pre_order_to_real[w]) {
            let Some(v) = real_to_pre_order[v] else {
                continue;
            };

            let x = eval(&mut parent, last_linked, &semi, &mut label, v);
            semi[w] = std::cmp::min(semi[w], semi[x]);
        }

        if parent[w] != semi[w] {
            bucket[semi[w]].push(w);
        } else {
            idom[w] = parent[w];
        }

        // Optimization: We share the parent array between processed and not
        // processed elements; last_linked represents the divider.
        last_linked = Some(w);
    }

    // Finalise the immediate dominators for any that were not fully settled during
    // the initial traversal.
    //
    // If `immediate_dominators[w] != semi[w]`, then we know that we've stored
    // vertex `y` from above ino `immediate_dominators[w]`. It is known to be
    // our "relative dominator", which means that it's one of `w`'s ancestors
    // and has the same immediate dominator as `w`, so use that as the immediate
    // dominator for `w`.
    for w in 1..reachable_vertices {
        let w = PreOrderIndex::new(w);

        if idom[w] != semi[w] {
            idom[w] = idom[idom[w]];
        }
    }

    let mut immediate_dominators = index_vec![None; graph.num_nodes()];
    for (index, node) in pre_order_to_real.iter_enumerated() {
        immediate_dominators[*node] = Some(pre_order_to_real[idom[index]]);
    }

    Dominators { post_order_rank, immediate_dominators }
}

#[cfg(test)]
mod test_super {
    use crate::graph::{dominators::dominators, tests::TestGraph};

    #[test]
    fn test_dominators_for_diamond() {
        let graph = TestGraph::new(0, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
        let dominators = dominators(&graph);

        let immediate_dominators = &dominators.immediate_dominators;

        assert_eq!(immediate_dominators[0].map(|i| i.index()), Some(0usize));
        assert_eq!(immediate_dominators[1].map(|i| i.index()), Some(0usize));
        assert_eq!(immediate_dominators[2].map(|i| i.index()), Some(0usize));
        assert_eq!(immediate_dominators[3].map(|i| i.index()), Some(0usize));
    }

    /// This tests the example from the paper (p. 122), which is a bit more
    /// complex.
    #[test]
    fn test_from_paper() {
        let graph = TestGraph::new(
            6,
            &[(6, 5), (6, 4), (5, 1), (4, 2), (4, 3), (1, 2), (2, 3), (3, 2), (2, 1)],
        );

        let dominators = dominators(&graph);
        let immediate_dominators = &dominators.immediate_dominators;
        assert_eq!(immediate_dominators[0].map(|i| i.index()), None); // <-- note that 0 is not in graph
        assert_eq!(immediate_dominators[1].map(|i| i.index()), Some(6));
        assert_eq!(immediate_dominators[2].map(|i| i.index()), Some(6));
        assert_eq!(immediate_dominators[3].map(|i| i.index()), Some(6));
        assert_eq!(immediate_dominators[4].map(|i| i.index()), Some(6));
        assert_eq!(immediate_dominators[5].map(|i| i.index()), Some(6));
        assert_eq!(immediate_dominators[6].map(|i| i.index()), Some(6));
    }
}
