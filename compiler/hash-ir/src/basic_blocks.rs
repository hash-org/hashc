//! Module that contains a manager for basic blocks of a particular
//! IR [Body]. The manager stores all of the basic blocks and provides
//! functionality for computing the predecessors and successors of
//! each basic block, and stores a cache on various traversal orders
//! of the stored basic blocks.

use std::{cell::OnceCell, fmt};

use index_vec::IndexVec;
use smallvec::{smallvec, SmallVec};

use crate::ir::{BasicBlock, BasicBlockData};

/// [BasicBlocks] is a manager for basic blocks of a particular
/// IR [Body]. The manager stores all of the basic blocks and provides
/// functionality for computing the predecessors and successors of
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

    /// Compute the predecessors of a basic block, or return the cached
    /// value if it has already been computed.
    pub fn predecessors_of(&self, block: BasicBlock) -> SmallVec<[BasicBlock; 4]> {
        self.predecessor_cache.compute(&self.blocks)[block].clone()
    }

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
