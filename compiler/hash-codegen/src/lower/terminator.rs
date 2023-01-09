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

use hash_abi::{ArgAbi, FnAbi, PassMode};
use hash_ir::ir::{self};

use super::{
    intrinsics::Intrinsic,
    locals::LocalRef,
    operands::{OperandRef, OperandValue},
    place::PlaceRef,
    FnBuilder,
};
use crate::{
    common::IntComparisonKind,
    traits::{
        builder::BlockBuilderMethods, constants::BuildConstValueMethods, ctx::HasCtxMethods,
        ty::BuildTypeMethods,
    },
};

/// [ReturnDestinationKind] defines the different ways that a
/// function call returns it's value, and which way the value
/// needs to be saved from the function call.
pub enum ReturnDestinationKind<V> {
    /// The return value is indirect or ignored.
    Nothing,

    /// The return value should be stored to the provided
    /// pointer.
    Store(PlaceRef<V>),

    /// Store an indirect return value to an operand local place.
    IndirectOperand(PlaceRef<V>, ir::Local),

    /// Store the return value to an operand local place.
    DirectOperand(ir::Local),
}

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
        block: ir::BasicBlock,
        terminator: &ir::Terminator,
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
            ir::TerminatorKind::Goto(_) => todo!(),
            ir::TerminatorKind::Call { op, ref args, destination, target } => {
                self.codegen_call_terminator(builder, op, args, destination, target, can_merge())
            }
            ir::TerminatorKind::Return => {
                self.codegen_return_terminator(builder);
                false
            }
            ir::TerminatorKind::Unreachable => {
                builder.unreachable();
                false
            }
            ir::TerminatorKind::Switch { ref value, ref targets } => {
                self.codegen_switch_terminator(builder, value, targets);
                false
            }
            ir::TerminatorKind::Assert { ref condition, expected, kind, target } => self
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
        target: ir::BasicBlock,
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
        _op: ir::Operand,
        _args: &[ir::Operand],
        _destination: ir::Place,
        _target: Option<ir::BasicBlock>,
        can_merge: bool,
    ) -> bool {
        can_merge
    }

    /// Emit code for a [`ir::TerminatorKind::Return`]. If the return type of
    /// the function is uninhabited, then this function will emit a
    /// `unreachable` instruction.
    // Additionally, unit types `()` are considered as a `void` return type.
    fn codegen_return_terminator(&mut self, builder: &mut Builder) {
        let layout = builder.layout_info(self.fn_abi.ret_abi.info.layout);

        // if the return type is uninhabited, then we can emit an
        // `abort` call to exit the program, and then close the
        // block with a `unreachable` instruction.
        if layout.abi.is_uninhabited() {
            builder.codegen_abort_intrinsic();
            builder.unreachable();

            return;
        }

        let value = match &self.fn_abi.ret_abi.mode {
            PassMode::Ignore | PassMode::Indirect { .. } => {
                builder.return_void();
                return;
            }
            PassMode::Direct(_) => {
                let op = self.codegen_consume_operand(
                    builder,
                    ir::Place::return_place(self.ctx.body_data()),
                );

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

    /// Emit code for a [`ir::TerminatorKind::Switch`]. This function will
    /// convert the `switch` into the relevant target backend IR. If the
    /// `switch` terminator represents an `if` statement, then the function
    /// will avoid generating an `switch` instruction and instead emit a
    /// single conditional jump.
    fn codegen_switch_terminator(
        &mut self,
        builder: &mut Builder,
        subject: &ir::Operand,
        targets: &ir::SwitchTargets,
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

    /// Emit code for an "assert" block terminator. This will create two
    /// branches, one where the assertion is not triggered, and the control
    /// flow continues, and the second block `failure_block` which contains
    /// a single function call to `panic` intrinsic, and which terminates
    /// the program.
    fn codegen_assert_terminator(
        &mut self,
        builder: &mut Builder,
        condition: &ir::Operand,
        expected: bool,
        assert_kind: ir::AssertKind,
        target: ir::BasicBlock,
        can_merge: bool,
    ) -> bool {
        let condition = self.codegen_operand(builder, condition).immediate_value();

        // try and evaluate the condition at compile time to determine
        // if we can avoid generating the panic block if the condition
        // is always true or false.
        let const_condition =
            builder.const_to_optional_u128(condition, false).map(|value| value == 1);

        if const_condition == Some(expected) {
            return self.codegen_goto_terminator(builder, target, can_merge);
        }

        // Add a hint for the condition as "expecting" the provided value
        let condition = builder.codegen_expect_intrinsic(condition, expected);

        // Create a failure blockm and a conditional branch to it.
        let failure_block = builder.append_sibling_block("assert_failure");
        let target = self.get_codegen_block_id(target);

        if expected {
            builder.conditional_branch(condition, target, failure_block);
        } else {
            builder.conditional_branch(condition, failure_block, target);
        }

        // It must be that after this point, the block goes to the `failure_block`
        builder.switch_to_block(failure_block);

        // we need to convert the assert into a message.
        let message = builder.const_str(assert_kind.message());
        let args = &[message.0, message.1];

        // @@Todo: we need to create a call to `panic`, as in resolve the funciton
        // abi to `panic` and the relative function pointer.
        let (fn_abi, fn_ptr) = self.resolve_intrinsic(builder, Intrinsic::Panic);

        // Finally we emit this as a call to panic...
        self.codegen_fn_call(builder, fn_abi, fn_ptr, args, None, false)
    }

    /// Function that prepares a function call to be generated, and the emits
    /// relevant code to execute the function, and deal with saving the
    /// function return value, and jumping to the next block on success or
    /// failure of the function.
    fn codegen_fn_call(
        &mut self,
        builder: &mut Builder,
        fn_abi: FnAbi,
        fn_ptr: Builder::Value,
        args: &[Builder::Value],
        destination: Option<(ir::BasicBlock, ReturnDestinationKind<Builder::Value>)>,
        can_merge: bool,
    ) -> bool {
        let fn_ty = builder.backend_type_from_abi(&fn_abi);

        //@@Future: when we deal with unwinding functions, we will have to use the
        // `builder::invoke()` API in order to instruct the backends to emit relevant
        // clean-up code for when the function starts to unwind (i.e. panic).
        // However for now, we simply emit a `builder::call()`
        let return_value = builder.call(fn_ty, Some(&fn_abi), fn_ptr, args);

        if let Some((destination_block, return_destination)) = destination {
            // we need to store the return value in the appropriate place.
            self.store_return_value(builder, return_destination, &fn_abi.ret_abi, return_value);
            self.codegen_goto_terminator(builder, destination_block, can_merge)
        } else {
            builder.unreachable();
            false
        }
    }

    /// Generates code that handles of how to save the return value from a
    /// function call.
    fn store_return_value(
        &mut self,
        builder: &mut Builder,
        destination: ReturnDestinationKind<Builder::Value>,
        return_abi: &ArgAbi,
        value: Builder::Value,
    ) {
        // @@DebugInfo: since is this where there is the possibility of locals
        // being assigned (direct/indirect), we need to generate debug information
        // for the fact that they were "introduced" here.

        match destination {
            ReturnDestinationKind::Nothing => {}
            ReturnDestinationKind::Store(destination) => {
                builder.store_arg(return_abi, value, destination)
            }
            ReturnDestinationKind::DirectOperand(local) => {
                // @@CastPassMode: if it is a casting pass mode, then it needs to be stored
                // as an alloca, then stored by `store_arg`m and then loaded, i.e. reloaded
                // of the stack.

                let op = OperandRef::from_immediate_value(value, return_abi.info);
                self.locals[local] = LocalRef::Operand(Some(op));
            }
            ReturnDestinationKind::IndirectOperand(temp, local) => {
                let op = builder.load_operand(temp);

                // declare that the `temporary` is now dead
                temp.storage_dead(builder);
                self.locals[local] = LocalRef::Operand(Some(op));
            }
        }
    }
}
