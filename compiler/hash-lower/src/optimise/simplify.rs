//! Contains the `simplification` pass which simplifies the control
//! flow graph by consiering the predecessors of each block and
//! whether:
//!
//! - If the block has no predecessors, it is unreachable, and therefore we can
//!   remove the block from the body, and potentially check if any of the
//!   successors of the block also become unreachable.
//!
//! - If a block has a single unconditional successor and no instructions, the
//!   destination of the block is propagated to all of the predecessor blocks
//!   pointing to the current block and updated. Once all of the predecessors
//!   have been updated, the current block is removed from the body.

use hash_ir::ir::{BasicBlock, Body, TerminatorKind};
use hash_pipeline::settings::{LoweringSettings, OptimisationLevel};

use super::IrOptimisation;
use crate::traversal;

/// Function that will iterate over all of the blocks and remove them
/// from the body source.
pub fn remove_dead_blocks(body: &mut Body) {
    let reachable_blocks = traversal::reachable_block_indices(body);
    let block_count = body.basic_blocks.len();

    // If all blocks are reachable, then we don't need to
    // anything.
    if reachable_blocks.ones().count() == block_count {
        return;
    }

    let basic_blocks = body.basic_blocks.blocks_mut();
    let mut replacement_map: Vec<_> = (0..block_count).map(BasicBlock::new).collect();
    let mut used_blocks = 0;

    for alive_index in reachable_blocks.ones() {
        replacement_map[alive_index] = BasicBlock::new(used_blocks);

        // We essentially fill in the next available block slot (dead block)
        // with the current alive block. This is okay to do since `alive_index`
        // will always be increasing.
        if alive_index != used_blocks {
            basic_blocks.raw.swap(alive_index, used_blocks);
        }

        used_blocks += 1;
    }

    // cleanup any remnants
    basic_blocks.raw.truncate(used_blocks);

    // now we need to go through and update all of the indices
    // of the block terminators with the terminators that are
    // specified within the replacement map.
    for block in basic_blocks {
        for target in block.terminator_mut().successors() {
            block.terminator_mut().replace_edge(target, replacement_map[target.index()])
        }
    }
}

pub struct SimplifyGraph;

impl IrOptimisation for SimplifyGraph {
    fn enabled(&self, settings: &LoweringSettings) -> bool {
        settings.optimisation_level >= OptimisationLevel::Release
    }

    fn optimise(&self, body: &mut Body) {
        // Firstly, lets check if there are any predecessors for each block. If the
        // block has no predecessors then we remove the block from the body entirely.
        // This is because the block is unreachable.
        //
        // It's safe not to invalidate the cache here since we are removing dead blocks.
        remove_dead_blocks(body);

        // Now we try to simplify the graph by removing blocks that only perform
        // a goto to another block. We perform this optimisation until we reached
        // a fixed point since it maybe be that we can remove multiple blocks in
        // a multiple iterations.
        loop {
            let mut changed = false;

            // stores the index of the block that can be removed, and the block
            // that it should be substituted with.
            let mut changes: Vec<(BasicBlock, BasicBlock)> = Vec::new();

            for (index, block) in body.blocks().iter_enumerated() {
                // If there are any statements in the block, or if the block is the
                // starting block, we cannot remove it since the entry point is
                // always the starting block.
                if !block.statements.is_empty()
                    || body.basic_blocks.predecessors_of(index).is_empty()
                {
                    continue;
                }

                if let TerminatorKind::Goto(substitution) = block.terminator.as_ref().unwrap().kind
                {
                    // we want to get all of the predecessors of this block, and substitute any
                    // references to the current block with the destination block.
                    changes.push((index, substitution));
                    changed = true;
                }
            }

            // Short-circuit if we didn't make any changes.
            if !changed {
                break;
            }

            // Now we can perform the changes to the body.
            for (index, substitution) in changes {
                let predecessors = body.basic_blocks.predecessors_of(index);

                for predecessor in predecessors {
                    if let Some(block) = body.basic_blocks.blocks_mut().get_mut(predecessor) {
                        let terminator = block.terminator.as_mut().unwrap();
                        terminator.replace_edge(index, substitution);
                    }
                }
            }

            // Now we can remove the blocks that we no longer need.
            remove_dead_blocks(body);
        }
    }
}
