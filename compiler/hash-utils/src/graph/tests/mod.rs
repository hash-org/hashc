//! This contains a definition for a test graph data structure. It
//! is intended that all algorithms that are implemented for graph
//! traversal and manipulation can be tested using a dummy [TestGraph].
#![allow(dead_code)] // This is allowed since we are using this for testing purposes.

use std::cmp::max;

use fxhash::FxHashMap;
use index_vec::define_index_type;

use super::WithPredecessors;

define_index_type! {
    /// A node within the graph.
    pub struct TestNode = usize;

    DEBUG_FORMAT = "TestNode({})";
    MAX_INDEX = usize::MAX;
    DISABLE_MAX_INDEX_CHECK = true;
}

pub(crate) struct TestGraph {
    /// The total number of nodes within the graph.
    node_count: usize,

    /// The starting index of the node.
    start_node: usize,

    /// The successors of each node in the graph.
    successors: FxHashMap<usize, Vec<usize>>,

    /// The predecessors of each node in the graph.
    predecessors: FxHashMap<usize, Vec<usize>>,
}

impl TestGraph {
    pub fn new(start_node: usize, nodes: &[(usize, usize)]) -> Self {
        let mut graph = TestGraph {
            node_count: start_node + 1,
            start_node,
            successors: FxHashMap::default(),
            predecessors: FxHashMap::default(),
        };

        for &(source, target) in nodes {
            graph.node_count = max(graph.node_count, source + 1);
            graph.node_count = max(graph.node_count, target + 1);

            // now insert entries for each target and source
            graph.successors.entry(source).or_default().push(target);
            graph.predecessors.entry(target).or_default().push(source);
        }

        // Ensure that we all nodes have successor and predecessor entries
        for node in 0..graph.node_count {
            graph.successors.entry(node).or_default();
            graph.predecessors.entry(node).or_default();
        }

        graph
    }
}

impl super::DirectedGraph for TestGraph {
    type Node = TestNode;

    fn num_nodes(&self) -> usize {
        self.node_count
    }

    fn start_node(&self) -> TestNode {
        TestNode::from_usize(self.start_node)
    }
}

impl super::GraphPredecessors<'_> for TestGraph {
    type Item = TestNode;
    type Iter = std::vec::IntoIter<TestNode>;
}

impl WithPredecessors for TestGraph {
    fn predecessors(&self, node: TestNode) -> <Self as super::GraphPredecessors>::Iter {
        let nodes = self.predecessors[&node.index()]
            .clone()
            .into_iter()
            .map(TestNode::from_usize)
            .collect::<Vec<_>>();

        nodes.into_iter()
    }
}

impl super::GraphSuccessors<'_> for TestGraph {
    type Item = TestNode;
    type Iter = std::vec::IntoIter<TestNode>;
}

impl super::WithSuccessors for TestGraph {
    fn successors(&self, node: TestNode) -> <Self as super::GraphSuccessors>::Iter {
        let nodes = self.successors[&node.index()]
            .clone()
            .into_iter()
            .map(TestNode::from_usize)
            .collect::<Vec<_>>();

        nodes.into_iter()
    }
}
