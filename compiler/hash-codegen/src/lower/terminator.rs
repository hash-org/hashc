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

use hash_abi::PassMode;
use hash_ir::ir::{BasicBlock, Operand, Place, SwitchTargets, Terminator, TerminatorKind};

use super::{operands::OperandValue, FnBuilder};
use crate::{
    common::IntComparisonKind,
    traits::{
        builder::BlockBuilderMethods, constants::BuildConstValueMethods, ctx::HasCtxMethods,
        ty::BuildTypeMethods,
    },
};

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

    /// Emit code for a [`TerminatorKind::Return`]. If the return type of the
    /// function is uninhabited, then this function will emit a
    /// `unreachable` instruction.
    // Additionally, unit types `()` are considered as a `void` return type.
    fn codegen_return_terminator(&mut self, builder: &mut Builder) {
        let layout = builder.layout_info(self.fn_abi.ret_abi.info.layout);

        // if the return type is uninhabited, then we can emit an
        // `abort` call to exit the program, and then close the
        // block with a `unreachable` instruction.
        if layout.abi.is_uninhabited() {
            builder.abort();
            builder.unreachable();

            return;
        }

        let value = match &self.fn_abi.ret_abi.mode {
            PassMode::Ignore | PassMode::Indirect { .. } => {
                builder.return_void();
                return;
            }
            PassMode::Direct(_) => {
                let op = self
                    .codegen_consume_operand(builder, Place::return_place(self.ctx.body_data()));

                if let OperandValue::Ref(value, alignment) = op.value {
                    let ty = builder.backend_type(op.info);
                    builder.load(ty, value, alignment)
                } else {
                    // @@Todo: deal with `Pair` operand refs
                    op.immediate_value()
                }
            }
        };

        builder.return_value(value);
    }

    /// Emit code for a [`TerminatorKind::Switch`]. This function will
    /// convert the `switch` into the relevant target backend IR. If the
    /// `switch` terminator represents an `if` statement, then the function
    /// will avoid generating an `switch` instruction and instead emit a
    /// single conditional jump.
    fn codegen_switch_terminator(
        &mut self,
        builder: &mut Builder,
        subject: &Operand,
        targets: &SwitchTargets,
    ) {
        let subject = self.codegen_operand(builder, subject);
        let ty = subject.info.ty;

        // If there are only two targets, then we can emit a single
        // conditional jump.
        let mut targets_iter = targets.iter();

        if targets_iter.len() == 1 {
            let (value, target) = targets_iter.next().unwrap();

            let true_block = self.get_codegen_block_id(target);
            let false_block = self.get_codegen_block_id(targets.otherwise());

            // If this type is a `bool`, then we can generate conditional
            // branches rather than an `icmp` and `br`.
            if self.ctx.body_data().tys().common_tys.bool == ty {
                match value {
                    0 => builder.conditional_branch(
                        subject.immediate_value(),
                        false_block,
                        true_block,
                    ),
                    1 => builder.conditional_branch(
                        subject.immediate_value(),
                        true_block,
                        false_block,
                    ),
                    _ => unreachable!(),
                }
            } else {
                // If this isn't a boolean type, then we have to emit an
                // `icmp` instruction to compare the subject value with
                // the target value.
                let subject_ty = builder.backend_type(subject.info);
                let target_value = builder.const_uint_big(subject_ty, value);
                let comparison =
                    builder.icmp(IntComparisonKind::Eq, subject.immediate_value(), target_value);
                builder.conditional_branch(comparison, true_block, false_block);
            }
        } else if targets_iter.len() == 2
            && self.body.blocks()[targets.otherwise()].is_empty_and_unreacheable()
        {
            // @@Todo: If the build is targeting "debug" mode, then we can
            // emit a `br` branch instead of switch to improve code generation
            // time on the (LLVM) backend.
            //
            // We should only do this for LLVM builds since this behaviour is specific
            // to LLVM. This means that we need to have access to `CodeGenSettings` here.
            todo!()
        } else {
            let otherwise_block = self.get_codegen_block_id(targets.otherwise());

            builder.switch(
                subject.immediate_value(),
                targets_iter.map(|(value, target)| (value, self.get_codegen_block_id(target))),
                otherwise_block,
            )
        }
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
