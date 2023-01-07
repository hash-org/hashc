//! This module hosts all of the logic for converting IR
//! [Terminator]s into corresponding target backend IR.
//! Given that the Hash IR does not necessarily have a
//! one-to-one mapping with the target IR, some terminators
//! might not exist in the target IR. For example, the
//! [TerminatorKind::Call] terminator might not exist in
//! some target IRs. In this case, the [TerminatorKind::Call],
//! is lowered as two [BasicBlock]s being "merged" together
//! into a single [BasicBlock]. The builder API will denote
//! whether two blocks have been merged together.

use hash_ir::ir::{BasicBlock, Operand, Place, SwitchTargets, Terminator, TerminatorKind};

use super::FnBuilder;
use crate::traits::builder::BlockBuilderMethods;

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {
    /// Emit the target backend IR for a Hash IR [Terminator]. This
    /// function returns whether the block is a candidate for merging
    /// with the next block. The conditions for merging two blocks
    /// must be:
    ///
    /// 1. The current block must be the only predecessor of the next
    ///   block.
    ///
    /// 2. The current block must only have a single successor which
    /// leads to the block that is a candidate for merging.
    pub(super) fn codegen_terminator(
        &mut self,
        builder: &mut Builder,
        block: BasicBlock,
        terminator: &Terminator,
    ) -> bool {
        let can_merge = || {
            let mut successors = terminator.successors();

            if let Some(successor) = successors.next() &&
                successors.next().is_none() &&
                let &[successor_pred] = self.body.basic_blocks.predecessors()[successor].as_slice()
            {
                // Ensure that the only predecessor of the successor is the current block.
                assert_eq!(successor_pred, block);
                true
            } else {
                false
            }
        };

        match terminator.kind {
            TerminatorKind::Goto(_) => todo!(),
            TerminatorKind::Call { op, ref args, destination, target } => {
                self.codegen_call_terminator(builder, op, args, destination, target, can_merge())
            }
            TerminatorKind::Return => {
                self.codegen_return_terminator(builder);
                false
            }
            TerminatorKind::Unreachable => {
                builder.unreachable();
                false
            }
            TerminatorKind::Switch { ref value, ref targets } => {
                self.codegen_switch_terminator(builder, value, targets);
                false
            }
            TerminatorKind::Assert { condition, expected, kind, target } => self
                .codegen_assert_terminator(builder, condition, expected, kind, target, can_merge()),
        }
    }

    /// Emit code for a [`TerminatorKind::Goto`]. This function will
    /// attempt to avoid emitting a `branch` if the blocks can be merged.
    ///
    /// Furthermore, this funciton can be used a general purpose method
    /// to emit code for unconditionally jumping from a block to another.
    fn codegen_goto_terminator(
        &mut self,
        builder: &mut Builder,
        target: BasicBlock,
        can_merge: bool,
    ) -> bool {
        // If we cannot merge the successor and this block, then
        // we have to emit a `br` to the successor target block.
        //
        // Otherwise, we can just return `true` to indicate that
        // the successor block can be merged with this block.
        if !can_merge {
            let target_block = self.get_codegen_block_id(target);
            builder.branch(target_block);
        }

        can_merge
    }

    fn codegen_call_terminator(
        &mut self,
        _builder: &mut Builder,
        _op: Operand,
        _args: &[Operand],
        _destination: Place,
        _target: Option<BasicBlock>,
        can_merge: bool,
    ) -> bool {
        can_merge
    }

    fn codegen_return_terminator(&mut self, _builder: &mut Builder) {
        todo!()
    }

    fn codegen_switch_terminator(
        &mut self,
        _builder: &mut Builder,
        _value: &Operand,
        _targets: &SwitchTargets,
    ) {
        todo!()
    }

    fn codegen_assert_terminator(
        &mut self,
        _builder: &mut Builder,
        _condition: hash_ir::ir::Operand,
        _expected: bool,
        _kind: hash_ir::ir::AssertKind,
        _target: BasicBlock,
        can_merge: bool,
    ) -> bool {
        can_merge
    }
}
