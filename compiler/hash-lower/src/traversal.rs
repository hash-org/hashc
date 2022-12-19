//! Contains useful utilities for traversing a CFG of
//! a particular body.

use fixedbitset::FixedBitSet;
use hash_ir::ir::{BasicBlock, BasicBlockData, Body, START_BLOCK};

/// A [PreOrder] struct contains the relevant information
/// about a pre-order traversal of a [Body]. This implements
/// the [Iterator] trait and will yield the next basic block
/// in the pre-order traversal.
pub struct PreOrder<'ir> {
    /// The body that we are traversing.
    body: &'ir Body,

    /// The visited blocks of the body.
    visited: FixedBitSet,

    /// The current work_list of the nodes that
    /// need to visited
    work_list: Vec<BasicBlock>,

    /// If the traversal orders starts at the beginning
    /// [START_BLOCK] of the body.
    root_is_start_block: bool,
}

impl<'ir> PreOrder<'ir> {
    /// Creates a new instance of [PreOrder] that will
    /// traverse the body in pre-order.
    pub fn new(body: &'ir Body, root: BasicBlock) -> Self {
        Self {
            body,
            visited: FixedBitSet::with_capacity(body.blocks().len()),
            work_list: vec![root],
            root_is_start_block: root == START_BLOCK,
        }
    }

    /// Create a new instance of [PreOrder] that will
    /// traverse the body in pre-order starting at the
    /// beginning [START_BLOCK] of the body.
    pub fn new_from_start(body: &'ir Body) -> Self {
        Self::new(body, START_BLOCK)
    }
}

impl<'ir> Iterator for PreOrder<'ir> {
    type Item = (BasicBlock, &'ir BasicBlockData);

    /// Implements the [Iterator] trait for [PreOrder]. Essentially
    /// traverses the body [BasicBlock]s in pre-order.
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.work_list.pop() {
            // Check if we have already visited this block, if not
            // then add it to the `visited` list and return this as
            // the next element of the graph traversal.
            if self.visited.contains(next.index()) {
                continue;
            } else {
                self.visited.insert(next.index());
            }

            let data = &self.body.blocks()[next];

            // Add all of the successors to the worklist so we
            // can visit them on the next iteration.
            if let Some(ref term) = data.terminator {
                self.work_list.extend(term.successors());
            }

            return Some((next, data));
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // All the blocks, minus the number of blocks we've visited.
        let upper = self.body.basic_blocks.len() - self.visited.ones().count();

        // If we start at the root, then we will visit all of the remaining
        // blocks in the body, otherwise we only visit the remaining blocks
        // in the `work_list`.
        let lower = if self.root_is_start_block { upper } else { self.work_list.len() };

        (lower, Some(upper))
    }
}

/// Compute reachable blocks from the [START_BLOCK] of the body.
pub(crate) fn reachable_block_indices(body: &Body) -> FixedBitSet {
    let mut pre_order_traversal = PreOrder::new_from_start(body);

    // now we perform the iteration, and only keep the visited blocks.
    (&mut pre_order_traversal).for_each(drop);

    pre_order_traversal.visited
}
