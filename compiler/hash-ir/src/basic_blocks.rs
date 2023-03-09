//! Module that contains a manager for basic blocks of a particular
//! IR [crate::ir::Body]. The manager stores all of the basic blocks and
//! provides functionality for computing the predecessors and successors of
//! each basic block, and stores a cache on various traversal orders
//! of the stored basic blocks.

use std::{cell::OnceCell, fmt};

use hash_utils::{
    graph::{
        self,
        dominators::{dominators, Dominators},
    },
    index_vec::IndexVec,
    smallvec::{smallvec, SmallVec},
};

use crate::ir::{BasicBlock, BasicBlockData, Successors};

/// [BasicBlocks] is a manager for basic blocks of a particular
/// IR [`crate::ir::Body`]. The manager stores all of the basic blocks and
/// provides functionality for computing the predecessors and successors of
/// each basic block, and stores a cache on various traversal orders
/// of the stored basic blocks.
pub struct BasicBlocks {
    /// The blocks that the function is represented with
    pub blocks: IndexVec<BasicBlock, BasicBlockData>,

    /// A cache that stores all of the predecessors of a block.
    predecessor_cache: PredecessorCache,
}

impl fmt::Debug for BasicBlocks {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (id, block) in self.blocks.iter_enumerated() {
            write!(f, "{id:?}")?;

            if let Some(terminator) = &block.terminator {
                writeln!(f, " -> {terminator:?}")?;
            } else {
                writeln!(f, " -> <none>")?;
            }
        }

        Ok(())
    }
}

impl BasicBlocks {
    /// Creates a new instance of [BasicBlocks].
    pub fn new(blocks: IndexVec<BasicBlock, BasicBlockData>) -> Self {
        Self { blocks, predecessor_cache: PredecessorCache::new() }
    }

    /// Check if the block count is zero.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// Get the length of the basic blocks.
    #[inline]
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    /// Get a mutable reference to the stored basic blocks. This does not
    /// invalidate any of the caches. Given that none of the caches are
    /// invalided, the following is assumed:
    ///
    ///  1) The number of basic blocks remains unchanged.
    ///  2) The set of successors of each terminator remains unchanged.
    ///
    /// If any of these conditions are violated, then the caller should
    /// invalidate all blocks that have been changed in order to either
    /// purge the cache of an entry or to update the entry if it is still
    /// required.
    #[inline]
    pub fn blocks_mut(&mut self) -> &mut IndexVec<BasicBlock, BasicBlockData> {
        // clear the cache
        self.clear_cache();

        &mut self.blocks
    }

    /// Compute all of the predecessors of this [BasicBlocks] graph.
    pub fn predecessors(&self) -> &Predecessors {
        self.predecessor_cache.compute(&self.blocks)
    }

    /// Compute all of the dominators of the this [BasicBlocks] graph.
    pub fn dominators(&self) -> Dominators<BasicBlock> {
        dominators(self)
    }

    /// Invalidate the cache for all [BasicBlock]s.
    pub fn clear_cache(&mut self) {
        self.predecessor_cache.invalidate();
    }

    /// Invalidate cache for a specific [BasicBlock].
    pub fn invalidate_cache_for(&mut self, block: BasicBlock) {
        self.predecessor_cache.cache.get_mut().unwrap()[block].clear();
    }
}

/// Represents the map of basic blocks to their predecessors.
///
/// Typically 95%+ of basic blocks have 4 or fewer predecessors.
pub type Predecessors = IndexVec<BasicBlock, SmallVec<[BasicBlock; 4]>>;

/// A wrapper around storing the predecessors of a basic block.
struct PredecessorCache {
    /// A cache that stores all of the predecessors of a block.
    pub cache: OnceCell<Predecessors>,
}

impl PredecessorCache {
    fn new() -> Self {
        Self { cache: OnceCell::new() }
    }

    pub fn invalidate(&mut self) {
        self.cache = OnceCell::new();
    }

    /// Compute the predecessors of a basic block, or return the cached
    /// value if it has already been computed.
    pub fn compute(&self, blocks: &IndexVec<BasicBlock, BasicBlockData>) -> &Predecessors {
        self.cache.get_or_init(|| {
            let mut predecessors = Predecessors::with_capacity(blocks.len());

            // we need to initialise all elements regardless of whether they
            // have any predecessors or not.
            for block in blocks.indices() {
                predecessors.insert(block, smallvec![]);
            }

            for (bb, data) in blocks.iter_enumerated() {
                for successor in data.successors() {
                    predecessors[successor].push(bb);
                }
            }

            predecessors
        })
    }
}

// Implement generic graph methods for [BasicBlocks].

impl graph::DirectedGraph for BasicBlocks {
    type Node = BasicBlock;

    fn num_nodes(&self) -> usize {
        self.len()
    }
}

impl<'s> graph::GraphSuccessors<'s> for BasicBlocks {
    type Item = BasicBlock;
    type Iter = Successors<'s>;
}

impl graph::WithSuccessors for BasicBlocks {
    fn successors(&self, node: BasicBlock) -> <Self as graph::GraphSuccessors>::Iter {
        self.blocks[node].terminator().successors()
    }
}

impl<'graph> graph::GraphPredecessors<'graph> for BasicBlocks {
    type Item = BasicBlock;
    type Iter = std::iter::Copied<std::slice::Iter<'graph, BasicBlock>>;
}

impl graph::WithPredecessors for BasicBlocks {
    fn predecessors(&self, node: Self::Node) -> <Self as graph::GraphPredecessors<'_>>::Iter {
        self.predecessors()[node].iter().copied()
    }
}
