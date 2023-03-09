//! Contains the `simplification` pass which simplifies the control
//! flow graph by considering the predecessors of each block and
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

use hash_ir::{
    ir::{BasicBlock, BasicBlockData, Body, Terminator, TerminatorKind, START_BLOCK},
    traversal, IrCtx,
};
use hash_pipeline::settings::{CompilerSettings, OptimisationLevel};
use hash_utils::{
    index_vec::{index_vec, Idx, IndexVec},
    smallvec::{smallvec, SmallVec},
};

use super::IrOptimisationPass;

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
        for target in block.terminator_mut().successors_mut() {
            *target = replacement_map[target.index()];
        }
    }
}

fn copy_index_vec<S, T: Clone, I: Idx>(value: T, previous: &IndexVec<I, S>) -> IndexVec<I, T> {
    index_vec![value; previous.len()]
}

/// This function is used to compute a predecessor count for each block, and
/// returns a vector of the counts. This is used to determine if a block has
/// a single predecessor, and therefore can be removed.
fn compute_predecessor_counts(body: &Body) -> IndexVec<BasicBlock, u32> {
    let mut counts = copy_index_vec(0, &body.basic_blocks.blocks);

    // We have to always set the count of the basic block as `1` since
    // it might not ever have any predecessors, but it is still reachable.
    counts[START_BLOCK] = 1;

    for (_, data) in traversal::PreOrder::new_from_start(body) {
        if let Some(ref term) = data.terminator {
            for target in term.successors() {
                counts[target] += 1;
            }
        }
    }

    counts
}

pub struct SimplifyGraph;

impl IrOptimisationPass for SimplifyGraph {
    fn name(&self) -> &'static str {
        "simplify-graph"
    }

    fn enabled(&self, settings: &CompilerSettings) -> bool {
        settings.optimisation_level >= OptimisationLevel::Debug
    }

    fn optimise(&self, body: &mut Body, _: &IrCtx) {
        GraphSimplifier::new(body).simplify();

        // Now we can remove the blocks that we no longer need.
        remove_dead_blocks(body);
    }
}

pub struct GraphSimplifier<'ir> {
    /// A reference to all of the basic blocks in the graph
    basic_blocks: &'ir mut IndexVec<BasicBlock, BasicBlockData>,

    /// A reference to the predecessor count for each block
    predecessor_count: IndexVec<BasicBlock, u32>,
}

impl<'ir> GraphSimplifier<'ir> {
    /// Create a new [`GraphSimplifier`] from the given body
    pub fn new(body: &'ir mut Body) -> Self {
        let predecessor_count = compute_predecessor_counts(body);

        GraphSimplifier { basic_blocks: body.basic_blocks.blocks_mut(), predecessor_count }
    }

    pub fn simplify(mut self) {
        // Now we try to simplify the graph by removing blocks that only perform
        // a goto to another block. We perform this optimisation until we reached
        // a fixed point since it maybe be that we can remove multiple blocks in
        // a multiple iterations.
        loop {
            let mut changed = false;

            for index in self.basic_blocks.indices() {
                // if this block has no predecessors, then we can just skip it
                if self.predecessor_count[index] == 0 {
                    continue;
                }

                let mut terminator = self.basic_blocks[index].terminator.take().unwrap();

                // attempt to simplify the goto chain
                for successor in terminator.successors_mut() {
                    self.fold_goto_chain(successor, &mut changed);
                }

                // @@Future: we could try to perform some optimisations with
                // merging blocks, and some branch simplification.

                // Reset the terminator of the block
                self.basic_blocks[index].terminator = Some(terminator);
            }

            // Short-circuit if we didn't make any changes.
            if !changed {
                break;
            }
        }
    }

    /// Traverse along a line of of goto chains and replace them with a single
    /// jump. These jump chains can occur in common with complex `match`
    /// expressions or `loop` control flow.
    fn fold_goto_chain(&mut self, block: &mut BasicBlock, changed: &mut bool) {
        // @@Note: usually the go-to chain will be of length 1, so we use a
        // smallvec here.
        let mut terminators: SmallVec<[_; 1]> = smallvec![];

        // Begin by traversing up the successor chain until we reach a
        // block that does not have a terminator which is a goto.
        let mut current = *block;

        while let Some(terminator) = self.take_terminator_on_goto(current) {
            let Terminator { kind: TerminatorKind::Goto(target), .. } = terminator else {
                unreachable!()
            };

            terminators.push((current, terminator));
            current = target;
        }

        let last = current;
        *block = last;

        // Now we iterate over all of the blocks that we have found to
        // be in the chain and update our `predecessor_count` to reflect
        // their removal.
        while let Some((current, mut terminator)) = terminators.pop() {
            let Terminator { kind: TerminatorKind::Goto (ref mut target), .. } = terminator else {
                unreachable!();
            };

            // update changed, and update the target
            *changed |= *target != last;
            *target = last;

            // If this is the last predecessor, then we don;t need to update
            // the count of the `target` since it will be removed.
            if self.predecessor_count[current] == 1 {
                self.predecessor_count[current] = 0;
            } else {
                self.predecessor_count[*target] += 1;
                self.predecessor_count[current] -= 1;
            }

            // finally, update the terminator of the current block
            self.basic_blocks[current].terminator = Some(terminator);
        }
    }

    /// Take the terminator from the given block, if it is a
    /// [TerminatorKind::Goto]. Additionally, the block must not have any
    /// statements since this may is not trivially collapsable.
    ///
    /// This is used continue traversing a goto chain.
    fn take_terminator_on_goto(&mut self, block: BasicBlock) -> Option<Terminator> {
        match self.basic_blocks[block] {
            BasicBlockData {
                ref statements,
                terminator:
                    ref mut terminator @ Some(Terminator { kind: TerminatorKind::Goto(_), .. }),
            } if statements.is_empty() => terminator.take(),
            _ => None,
        }
    }
}
