//! This module hosts all of the logic for converting IR
//! [ir::Terminator]s into corresponding target backend IR.
//! Given that the Hash IR does not necessarily have a
//! one-to-one mapping with the target IR, some terminators
//! might not exist in the target IR. For example, the
//! [`ir::TerminatorKind::Call`] terminator might not exist in
//! some target IRs. In this case, the [ir::TerminatorKind::Call],
//! is lowered as two [ir::BasicBlock]s being "merged" together
//! into a single [ir::BasicBlock]. The builder API will denote
//! whether two blocks have been merged together.

use hash_abi::{ArgAbi, FnAbiId, PassMode};
use hash_ir::{intrinsics::Intrinsic, ir, lang_items::LangItem, ty::COMMON_IR_TYS};
use hash_pipeline::settings::{CodeGenBackend, OptimisationLevel};
use hash_storage::store::{statics::StoreId, Store};
use hash_target::abi::{AbiRepresentation, ValidScalarRange};

use super::{
    locals::LocalRef,
    operands::{OperandRef, OperandValue},
    place::PlaceRef,
    utils::mem_copy_ty,
    FnBuilder,
};
use crate::{
    common::{IntComparisonKind, MemFlags},
    traits::{
        builder::BlockBuilderMethods, constants::ConstValueBuilderMethods,
        misc::MiscBuilderMethods, ty::TypeBuilderMethods, HasCtxMethods,
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

impl<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> FnBuilder<'a, 'b, Builder> {
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

            if let Some(successor) = successors.next()
                && successors.next().is_none()
                && let &[successor_pred] =
                    self.body.basic_blocks.predecessors()[successor].as_slice()
            {
                // Ensure that the only predecessor of the successor is the current block.
                assert_eq!(successor_pred, block);
                true
            } else {
                false
            }
        };

        match &terminator.kind {
            ir::TerminatorKind::Goto(target) => {
                self.codegen_goto_terminator(builder, *target, can_merge())
            }
            ir::TerminatorKind::Call { ref op, ref args, destination, target } => {
                self.codegen_call_terminator(builder, op, args, *destination, *target, can_merge())
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
                .codegen_assert_terminator(
                    builder,
                    condition,
                    *expected,
                    kind.as_ref(),
                    *target,
                    can_merge(),
                ),
        }
    }

    /// Emit code for a [`TerminatorKind::Goto`]. This function will
    /// attempt to avoid emitting a `branch` if the blocks can be merged.
    ///
    /// Furthermore, this function can be used a general purpose method
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

    /// Emit code for a call terminator. This function will emit code
    /// for a function call.
    fn codegen_call_terminator(
        &mut self,
        builder: &mut Builder,
        op: &ir::Operand,
        fn_args: &[ir::Operand],
        destination: ir::Place,
        target: Option<ir::BasicBlock>,
        can_merge: bool,
    ) -> bool {
        // generate the operand as the function call...
        let call_subject = self.codegen_operand(builder, op);

        let ty = call_subject.info.ty;
        let instance = ty.borrow().as_instance();
        let is_intrinsic = instance.borrow().is_intrinsic();
        let mut maybe_intrinsic = None;

        // If this is an intrinsic, we will generate the required code
        // for the intrinsic here...
        if is_intrinsic {
            maybe_intrinsic = Intrinsic::from_str_name(instance.borrow().name().into());

            // We exit early for transmute since we don't need to compute the ABI
            // or any information about the return destination.
            if let Some(Intrinsic::Transmute) = maybe_intrinsic {
                return if let Some(target) = target {
                    let src = self.codegen_operand(builder, &fn_args[2]);

                    match self.locals[destination.local] {
                        LocalRef::Place(_) => {
                            let dest = self.codegen_place(builder, destination);
                            self.codegen_transmute(builder, src, dest);
                        }
                        LocalRef::Operand(Some(op)) => {
                            self.codegen_transmute_operand(builder, src, op.info);
                        }
                        LocalRef::Operand(None) => {
                            let info = self.compute_place_ty_info(builder, destination);
                            let operand =
                                self.codegen_transmute_operand(builder, src, info).unwrap();
                            let or = OperandRef { info, value: operand };

                            self.locals[destination.local] = LocalRef::Operand(Some(or));
                        }
                    }
                    self.codegen_goto_terminator(builder, target, can_merge)
                } else {
                    builder.unreachable();
                    false
                };
            }
        }

        // compute the function pointer value and the ABI
        let abis = self.ctx.cg_ctx().abis();
        let fn_abi = abis.create_fn_abi(builder, instance);
        let ret_abi = abis.map_fast(fn_abi, |abi| abi.ret_abi);

        // If the return ABI pass mode is "indirect", then this means that
        // we have to create a temporary in order to represent the "out_ptr"
        // of the function.
        let mut args = Vec::with_capacity(fn_args.len() + (ret_abi.is_indirect() as usize));

        // compute the return destination of the function. If the function
        // return is indirect, `compute_fn_return_destination` will push
        // an operand which represents the "out_ptr" as the first argument.
        let return_destination = if target.is_some() {
            self.compute_fn_return_destination(builder, destination, &ret_abi, &mut args, false)
        } else {
            ReturnDestinationKind::Nothing
        };

        // Keep track of all of the copied "constant" arguments to a function
        // if the value is being passed as a reference.
        let mut copied_const_args = vec![];

        // Deal with the function arguments
        for (index, arg) in fn_args.iter().enumerate() {
            let mut arg_operand = self.codegen_operand(builder, arg);

            if let (ir::Operand::Const(_), OperandValue::Ref(_, _)) = (arg, arg_operand.value) {
                let temp = PlaceRef::new_stack(builder, arg_operand.info);
                let size = arg_operand.info.size();

                builder.lifetime_start(temp.value, size);
                arg_operand.value.store(builder, temp);
                arg_operand.value = OperandValue::Ref(temp.value, temp.alignment);

                copied_const_args.push(temp);
            }

            let arg_abi = abis.get_arg_abi(fn_abi, index);
            self.codegen_fn_argument(builder, arg_operand, &mut args, &arg_abi);
        }

        // If we have an intrinsic, then we will generate the appropriate code
        // for the intrinsic through the `codegen_intrinsic` function.
        if let Some(intrinsic) = maybe_intrinsic {
            let destination = match return_destination {
                _ if ret_abi.is_indirect() => args[0],
                ReturnDestinationKind::Nothing => builder.const_undef(builder.type_ptr()),
                ReturnDestinationKind::IndirectOperand(op, _)
                | ReturnDestinationKind::Store(op) => op.value,
                ReturnDestinationKind::DirectOperand(_) => {
                    panic!("direct operand being used for intrinsic call")
                }
            };

            let op_args =
                fn_args.iter().map(|arg| self.codegen_operand(builder, arg)).collect::<Vec<_>>();

            if let Some(Intrinsic::Memcmp) = maybe_intrinsic {
                abis.map_fast(fn_abi, |abi| {
                    builder.codegen_intrinsic_call(ty, abi, &args, destination);
                })
            } else {
                self.codegen_intrinsic(builder, intrinsic, &ret_abi, &op_args, destination)
            }

            if let ReturnDestinationKind::IndirectOperand(dest, _) = return_destination {
                self.store_return_value(builder, return_destination, &ret_abi, dest.value);
            }

            return if target.is_some() {
                true
            } else {
                builder.unreachable();
                false
            };
        }

        let fn_ptr = builder.get_fn_ptr(instance);

        // Finally, generate the code for the function call and
        // cleanup
        self.codegen_fn_call(
            builder,
            fn_abi,
            fn_ptr,
            &args,
            &copied_const_args,
            target.as_ref().map(|&target| (target, return_destination)),
            can_merge,
        )
    }

    /// Emit code for a function argument. Depending on the [PassMode] of
    /// the argument ABI, this may change what code is generated for the
    /// particular argument.
    fn codegen_fn_argument(
        &mut self,
        builder: &mut Builder,
        arg: OperandRef<Builder::Value>,
        args: &mut Vec<Builder::Value>,
        arg_abi: &ArgAbi,
    ) {
        match arg_abi.mode {
            // We don't need to do anything if the argument is ignored.
            PassMode::Ignore => return,

            // If it's a pair, we just push the args and return since we don't need
            // do anything special for.
            PassMode::Pair(_, _) => match arg.value {
                OperandValue::Pair(a, b) => {
                    args.push(a);
                    args.push(b);
                    return;
                }
                _ => unreachable!("invalid pair value for argument"),
            },
            _ => {}
        }

        // Despite something being an immediate value, if it is passed
        // indirectly, we have to force to be passed by reference.
        let (mut value, alignment, by_ref) = match arg.value {
            OperandValue::Immediate(_) | OperandValue::Pair(_, _) => match arg_abi.mode {
                PassMode::Indirect { .. } => {
                    let temp = PlaceRef::new_stack(builder, arg_abi.info);
                    arg.value.store(builder, temp);

                    (temp.value, temp.alignment, true)
                }
                _ => {
                    let abi_alignment = arg_abi.info.abi_alignment();
                    (arg.immediate_or_scalar_pair(builder), abi_alignment, false)
                }
            },
            OperandValue::Zero => match arg_abi.mode {
                PassMode::Indirect { on_stack, .. } => {
                    if on_stack {
                        panic!("zst `{arg:?}` was passed with abi `{arg_abi:?}`");
                    }

                    let temp = PlaceRef::new_stack(builder, arg_abi.info);
                    (temp.value, temp.alignment, true)
                }
                mode => panic!("zst wasn't ignored, pass with `{mode:?}`"),
            },
            OperandValue::Ref(value, alignment) => {
                let abi_alignment = arg_abi.info.abi_alignment();

                // If the argument is indirect, and the alignment of the operand is
                // smaller than the ABI alignment, then we need to put this value in a
                // temporary with the ABI argument layout.
                if arg_abi.is_indirect() && alignment < abi_alignment {
                    let temp = PlaceRef::new_stack(builder, arg_abi.info);

                    mem_copy_ty(
                        builder,
                        (temp.value, temp.alignment),
                        (value, alignment),
                        arg.info,
                        MemFlags::empty(),
                    );
                    (temp.value, temp.alignment, true)
                } else {
                    (value, alignment, true)
                }
            }
        };

        if by_ref && !arg_abi.is_indirect() {
            // @@CastPassMode: here we might have to deal with a casting pass mode
            // which means that we load the operand and then cast it

            // If it is direct, Here, we know that this value must be a boolean. In
            // the case that it is a boolean, we add additional metadata to the scalar
            // value, and convert the `value` to an immediate bool for LLVM (other backends
            // don't do anything and it's just a NOP).
            //
            if matches!(arg_abi.mode, PassMode::Direct(..)) {
                value = builder.load(builder.backend_ty_from_info(arg_abi.info), value, alignment);

                let layout_abi = arg_abi.info.layout.borrow().abi;

                if let AbiRepresentation::Scalar(scalar_kind) = layout_abi {
                    if scalar_kind.is_bool() {
                        builder.add_range_metadata_to(value, ValidScalarRange { start: 0, end: 1 });
                    }

                    // @@Performance: we could just pass a ptr to layout here??
                    value = builder.to_immediate(value, arg_abi.info.layout);
                }
            }
        }

        // Push the value that was generated
        args.push(value);
    }

    /// Compute the kind of operation that is required when callers deal
    /// with the return value of a function. For example, it is possible for the
    /// return value of a function to be ignored (and thus nothing happens),
    /// or if the value is indirect which means that it will be passed
    /// through an argument to the function rather than the actual pointer
    /// directly ( which is then represented as a
    /// [`ReturnDestinationKind::Store`]).
    pub(super) fn compute_fn_return_destination(
        &mut self,
        builder: &mut Builder,
        destination: ir::Place,
        return_abi: &ArgAbi,
        fn_args: &mut Vec<Builder::Value>,
        is_intrinsic: bool,
    ) -> ReturnDestinationKind<Builder::Value> {
        // We don't need to do anything if the return value is ignored.
        if return_abi.is_ignored() {
            return ReturnDestinationKind::Nothing;
        }

        let destination = if let Some(local) = destination.as_local() {
            match self.locals[local] {
                LocalRef::Place(destination) => destination,
                LocalRef::Operand(None) => {
                    // If the return value is specified as indirect, but the value is
                    // a local, we have to push into a stack slot.
                    //
                    // Or, intrinsics need a place to store their result due to it being
                    // unclear on how to transfer the result directly...
                    //
                    return if return_abi.is_indirect() || is_intrinsic {
                        let temp = PlaceRef::new_stack(builder, return_abi.info);
                        temp.storage_live(builder);
                        ReturnDestinationKind::IndirectOperand(temp, local)
                    } else {
                        ReturnDestinationKind::DirectOperand(local)
                    };
                }
                LocalRef::Operand(Some(_)) => panic!("return place already assigned to"),
            }
        } else {
            self.codegen_place(builder, destination)
        };

        // If the return value is specified as indirect, the value
        // is passed through the argument and not the return type...
        if return_abi.is_indirect() {
            fn_args.push(destination.value);
            ReturnDestinationKind::Nothing
        } else {
            // Otherwise the caller must store/read it from the
            // computed destination.
            ReturnDestinationKind::Store(destination)
        }
    }

    /// Emit code for a [`ir::TerminatorKind::Return`]. If the return type of
    /// the function is uninhabited, then this function will emit a
    /// `unreachable` instruction.
    // Additionally, unit types `()` are considered as a `void` return type.
    fn codegen_return_terminator(&mut self, builder: &mut Builder) {
        let ret_abi = builder.cg_ctx().abis().get_return_abi(self.fn_abi);
        let is_uninhabited = ret_abi.info.layout.borrow().abi.is_uninhabited();

        // if the return type is uninhabited, then we can emit an
        // `abort` call to exit the program, and then close the
        // block with a `unreachable` instruction.
        if is_uninhabited {
            builder.codegen_abort_intrinsic();
            builder.unreachable();

            return;
        }

        let value = match &ret_abi.mode {
            PassMode::Ignore | PassMode::Indirect { .. } => {
                builder.return_void();
                return;
            }
            PassMode::Direct(_) | PassMode::Pair(..) => {
                let op = self.codegen_consume_operand(builder, ir::Place::return_place());

                if let OperandValue::Ref(value, alignment) = op.value {
                    let ty = builder.backend_ty_from_info(op.info);
                    builder.load(ty, value, alignment)
                } else {
                    op.immediate_or_scalar_pair(builder)
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
            if COMMON_IR_TYS.bool == ty {
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
                let subject_ty = builder.backend_ty_from_info(subject.info);
                let target_value = builder.const_uint_big(subject_ty, value);
                let comparison =
                    builder.icmp(IntComparisonKind::Eq, subject.immediate_value(), target_value);
                builder.conditional_branch(comparison, true_block, false_block);
            }
            // If the build is targeting "debug" mode, then we can
            // emit a `br` branch instead of switch to improve code generation
            // time on the (LLVM) backend. On debug builds, LLVM will use the
            // [FastISel](https://llvm.org/doxygen/classllvm_1_1FastISel.html) block
            // for dealing with `br` instructions, which is faster on debug than
            // switches.
            //
            // This only applies to debug builds, as `FastISel` should not be
            // used on release builds as it looses some potential
            // optimisations.
            //
            // This optimisation comes from the "rustc" compiler:
            //
            // Ref: https://cs.github.com/rust-lang/rust/blob/3020239de947ec52677e9b4e853a6a9fc073d1f9/compiler/rustc_codegen_ssa/src/mir/block.rs#L335
        } else if targets_iter.len() == 2
            && self.body.blocks()[targets.otherwise()].is_empty_and_unreachable()
            && self.ctx.settings().optimisation_level == OptimisationLevel::Debug
            && self.ctx.settings().codegen_settings().backend == CodeGenBackend::LLVM
        {
            let (value, target_1) = targets_iter.next().unwrap();
            let (_, target_2) = targets_iter.next().unwrap();

            let target_block_1 = self.get_codegen_block_id(target_1);
            let target_block_2 = self.get_codegen_block_id(target_2);

            let subject_ty = builder.immediate_backend_ty(builder.layout_of(ty));
            let target_value = builder.const_uint_big(subject_ty, value);
            let comparison =
                builder.icmp(IntComparisonKind::Eq, subject.immediate_value(), target_value);
            builder.conditional_branch(comparison, target_block_1, target_block_2);
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
        assert_kind: &ir::AssertKind,
        target: ir::BasicBlock,
        can_merge: bool,
    ) -> bool {
        let condition_operand = self.codegen_operand(builder, condition).immediate_value();

        // try and evaluate the condition at compile time to determine
        // if we can avoid generating the panic block if the condition
        // is always true or false.
        let const_condition =
            builder.const_to_optional_u128(condition_operand, false).map(|value| value == 1);

        if const_condition == Some(expected) {
            return self.codegen_goto_terminator(builder, target, can_merge);
        }

        // Add a hint for the condition as "expecting" the provided value
        let condition = builder.codegen_expect_intrinsic(condition_operand, expected);

        // Create a failure block and a conditional branch to it.
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
        let (bytes, len) = builder.const_str(assert_kind.message().into());
        let args: [Builder::Value; 2] = (bytes, len).into();

        // Get the `panic` lang item.
        let (instance, fn_ptr) = self.resolve_lang_item(builder, LangItem::Panic);
        let abi = self.ctx.cg_ctx().abis().create_fn_abi(builder, instance);

        // Finally we emit this as a call to panic...
        self.codegen_fn_call(builder, abi, fn_ptr, &args, &[], None, false)
    }

    /// Function that prepares a function call to be generated, and the emits
    /// relevant code to execute the function, and deal with saving the
    /// function return value, and jumping to the next block on success or
    /// failure of the function.
    #[allow(clippy::too_many_arguments)]
    fn codegen_fn_call(
        &mut self,
        builder: &mut Builder,
        fn_abi: FnAbiId,
        fn_ptr: Builder::Function,
        args: &[Builder::Value],
        copied_const_args: &[PlaceRef<Builder::Value>],
        destination: Option<(ir::BasicBlock, ReturnDestinationKind<Builder::Value>)>,
        can_merge: bool,
    ) -> bool {
        //@@Future: when we deal with unwinding functions, we will have to use the
        // `builder::invoke()` API in order to instruct the backends to emit relevant
        // clean-up code for when the function starts to unwind (i.e. panic).
        // However for now, we simply emit a `builder::call()`
        let return_value = builder.call(fn_ptr, args, Some(fn_abi));

        if let Some((destination_block, return_destination)) = destination {
            // now that the function has finished, we essentially mark all of the
            // copied constants as being "dead"...
            for temporary in copied_const_args {
                let size = temporary.info.size();
                builder.lifetime_end(temporary.value, size)
            }

            let ret_abi = self.ctx.cg_ctx().abis().get_return_abi(fn_abi);

            // we need to store the return value in the appropriate place.
            self.store_return_value(builder, return_destination, &ret_abi, return_value);
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
                builder.store_fn_call_arg(return_abi, value, destination)
            }
            ReturnDestinationKind::DirectOperand(local) => {
                // @@CastPassMode: if it is a casting pass mode, then it needs to be stored
                // as an alloca, then stored by `store_arg`m and then loaded, i.e. reloaded
                // of the stack.

                let op = OperandRef::from_immediate_value_or_scalar_pair(
                    builder,
                    value,
                    return_abi.info,
                );
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
