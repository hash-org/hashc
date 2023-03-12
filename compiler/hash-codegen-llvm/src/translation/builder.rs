//! Implementation for all of the specified methods of
//! [hash_codegen::traits::builder::BlockBuilderMethods] using the Inkwell
//! wrapper around LLVM.

use std::{borrow::Cow, ffi::CString, iter};

use hash_codegen::{
    abi::FnAbi,
    common::{AtomicOrdering, CheckedOp, IntComparisonKind, MemFlags, RealComparisonKind},
    layout::TyInfo,
    lower::{
        operands::{OperandRef, OperandValue},
        place::PlaceRef,
    },
    traits::{
        builder::BlockBuilderMethods, constants::ConstValueBuilderMethods, ctx::HasCtxMethods,
        layout::LayoutMethods, ty::TypeBuilderMethods,
    },
};
use hash_ir::ty::{IrTy, IrTyId};
use hash_source::constant::{IntTy, SIntTy, UIntTy};
use hash_target::{
    abi::{AbiRepresentation, Scalar, ScalarKind, ValidScalarRange},
    alignment::Alignment,
    size::Size,
};
use inkwell::{
    basic_block::BasicBlock,
    types::{AnyType, AnyTypeEnum, AsTypeRef, BasicTypeEnum},
    values::{
        AggregateValueEnum, AnyValue, AnyValueEnum, AsValueRef, BasicMetadataValueEnum, BasicValue,
        BasicValueEnum, FunctionValue, InstructionValue, IntMathValue, IntValue, PhiValue,
        UnnamedAddress,
    },
};
use llvm_sys::core::{LLVMBuildExactUDiv, LLVMGetTypeKind};
use rayon::iter::Either;

use super::{
    abi::ExtendedFnAbiMethods, layouts::ExtendedLayoutMethods, ty::ExtendedTyBuilderMethods,
    Builder,
};
use crate::misc::{
    AtomicOrderingWrapper, FloatPredicateWrapper, IntPredicateWrapper, MetadataTypeKind,
};

/// Convert a [AnyValueEnum] to a [InstructionValue] by first
/// converting it into a basic value, and then using the proper
/// projection function to get it as an instruction value. This
/// function overrides the default behaviour of [AnyValueEnum] which
/// panics if the value is not an [`AnyValueEnum::InstructionValue`] which
/// is not always correct to do.
///
/// N.B. If the value does not come from an instruction, this function
/// will panic.
pub fn instruction_from_any_value(value: AnyValueEnum<'_>) -> InstructionValue<'_> {
    let value: BasicValueEnum = value.try_into().unwrap();
    value.as_instruction_value().unwrap()
}

impl<'a, 'b, 'm> Builder<'a, 'b, 'm> {
    /// Create a PHI node in the current block.
    fn phi(
        &mut self,
        ty: AnyTypeEnum<'m>,
        values: &[&dyn BasicValue<'m>],
        blocks: &[BasicBlock<'m>],
    ) -> PhiValue<'m> {
        debug_assert_eq!(values.len(), blocks.len());

        // Create the PHI value, and then add all of the incoming values.
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        let phi = self.builder.build_phi(ty, "phi");

        // @@Efficiency: patch inkwell to allow to provide these references directly...
        let blocks_and_values = blocks
            .iter()
            .zip(values.iter())
            .map(|(block, value)| (*value, *block))
            .collect::<Vec<_>>();

        phi.add_incoming(blocks_and_values.as_slice());
        phi
    }

    /// Add incoming values to a PHI node.
    fn add_incoming_to_phi(&mut self, phi: PhiValue, value: BasicValueEnum, block: BasicBlock) {
        phi.add_incoming(&[(&value, block)]);
    }

    /// Check and just function call arguments. If the argument and parameter
    /// types mismatch, the function will automatically insert bitcasts to
    /// adjust the arguments.
    fn check_call_args<'arg>(
        &mut self,
        func: FunctionValue<'m>,
        args: &'arg [BasicMetadataValueEnum<'m>],
    ) -> Cow<'arg, [BasicMetadataValueEnum<'m>]> {
        let func_params = func.get_type().get_param_types();

        // Check if all arguments match, and if so we return
        // early.
        let all_args_match = args.iter().zip(func_params.iter()).all(|(arg, param)| {
            let ty: BasicTypeEnum = self.ty_of_value(arg.as_any_value_enum()).try_into().unwrap();
            ty == *param
        });

        if all_args_match {
            return Cow::Borrowed(args);
        }

        let casted_args: Vec<_> = iter::zip(func_params, args)
            .map(|(expected_ty, &actual_val)| {
                let actual_ty = self.ty_of_value(actual_val.as_any_value_enum());

                if expected_ty != actual_ty.try_into().unwrap() {
                    self.bit_cast(actual_val.as_any_value_enum(), expected_ty.as_any_type_enum())
                        .try_into()
                        .unwrap()
                } else {
                    actual_val
                }
            })
            .collect();

        Cow::Owned(casted_args)
    }
}

impl<'a, 'b, 'm> BlockBuilderMethods<'a, 'b> for Builder<'a, 'b, 'm> {
    fn ctx(&self) -> &Self::CodegenCtx {
        self.ctx
    }

    fn build(ctx: &'a Self::CodegenCtx, block: Self::BasicBlock) -> Self {
        let builder = ctx.ll_ctx.create_builder();

        // We need to set the insertion point to the end of the block
        // because the builder is created at the beginning of the block.
        builder.position_at_end(block);

        Builder { builder, ctx }
    }

    fn append_block(
        ctx: &'a Self::CodegenCtx,
        func: Self::Function,
        name: &str,
    ) -> Self::BasicBlock {
        ctx.ll_ctx.append_basic_block(func, name)
    }

    fn append_sibling_block(&mut self, name: &str) -> Self::BasicBlock {
        let func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
        Self::append_block(self.ctx, func, name)
    }

    fn basic_block(&self) -> Self::BasicBlock {
        self.builder.get_insert_block().unwrap()
    }

    fn switch_to_block(&mut self, block: Self::BasicBlock) {
        *self = Self::build(self.ctx, block);
    }

    fn return_value(&mut self, value: Self::Value) {
        let value: BasicValueEnum = value.try_into().unwrap();
        self.builder.build_return(Some(&value));
    }

    fn return_void(&mut self) {
        self.builder.build_return(None);
    }

    fn branch(&mut self, destination: Self::BasicBlock) {
        self.builder.build_unconditional_branch(destination);
    }

    fn conditional_branch(
        &mut self,
        condition: Self::Value,
        true_block: Self::BasicBlock,
        false_block: Self::BasicBlock,
    ) {
        // @@Verify: is it always meant to be an int-value comparison.
        let value = condition.into_int_value();
        self.builder.build_conditional_branch(value, true_block, false_block);
    }

    fn switch(
        &mut self,
        condition: Self::Value,
        cases: impl ExactSizeIterator<Item = (u128, Self::BasicBlock)>,
        otherwise_block: Self::BasicBlock,
    ) {
        // @@Verify: is it always meant to be an int-value comparison.
        let value = condition.into_int_value();

        // Create all of the case-branch pairs.
        let cases = cases.map(|(value, block)| {
            let AnyValueEnum::IntValue(val) = self.const_uint_big(condition.get_type(), value) else {
                unreachable!()
            };

            (val, block)
        }).collect::<Vec<_>>();

        self.builder.build_switch(value, otherwise_block, &cases);
    }

    fn unreachable(&mut self) {
        self.builder.build_unreachable();
    }

    fn call(
        &mut self,
        fn_ptr: Self::Function,
        args: &[Self::Value],
        fn_abi: Option<&FnAbi>,
    ) -> Self::Value {
        let args: Vec<BasicMetadataValueEnum> =
            args.iter().map(|v| (*v).try_into().unwrap()).collect();

        // The call adjustment might modify the arguments by inserting
        // bitcasts...
        let args = self.check_call_args(fn_ptr, &args);
        let site = self.builder.build_call(fn_ptr, &args, "");

        if let Some(abi) = fn_abi {
            abi.apply_attributes_call_site(self, site);
        }

        // Convert the `CallSiteValue` into a `AnyEnumValue`...
        //
        // @@Cleanup: maybe patch inkwell with this func?
        match site.try_as_basic_value() {
            Either::Left(val) => val.into(),
            Either::Right(val) => val.into(),
        }
    }

    // @@Todo: would be nice to make this a macro...

    fn add(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_add(lhs, rhs, "").into()
    }

    fn fadd(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_float_value();
        let rhs = rhs.into_float_value();

        self.builder.build_float_add(lhs, rhs, "").into()
    }

    fn fadd_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_float_value();
        let rhs = rhs.into_float_value();

        let value = self.builder.build_float_add(lhs, rhs, "");

        // @@Todo: set the `fast` metadata flag on this operation
        // value.as_instruction().map(|instruction| instruction.set_metadata(metadata,
        // kind_id));
        value.into()
    }

    fn sub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_sub(lhs, rhs, "").into()
    }

    fn fsub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_float_value();
        let rhs = rhs.into_float_value();

        self.builder.build_float_sub(lhs, rhs, "").into()
    }

    fn fsub_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_float_value();
        let rhs = rhs.into_float_value();

        let value = self.builder.build_float_sub(lhs, rhs, "");

        // @@Todo: set the `fast` metadata flag on this operation
        // value.as_instruction().map(|instruction| instruction.set_metadata(metadata,
        // kind_id));
        value.into()
    }

    fn mul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_mul(lhs, rhs, "").into()
    }

    fn fmul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_float_value();
        let rhs = rhs.into_float_value();

        self.builder.build_float_mul(lhs, rhs, "").into()
    }

    fn fmul_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_float_value();
        let rhs = rhs.into_float_value();

        let value = self.builder.build_float_mul(lhs, rhs, "");

        // @@Todo: set the `fast` metadata flag on this operation
        // value.as_instruction().map(|instruction| instruction.set_metadata(metadata,
        // kind_id));
        value.into()
    }

    fn udiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_unsigned_div(lhs, rhs, "").into()
    }

    fn exactudiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        // @@Todo: patch inkwell to allow for exact unsigned division

        // create an empty c_str
        let c_string = CString::new("").unwrap();

        let value = unsafe {
            LLVMBuildExactUDiv(
                self.builder.as_mut_ptr(),
                lhs.as_value_ref(),
                rhs.as_value_ref(),
                c_string.as_ptr(),
            )
        };

        unsafe { IntValue::new(value) }.into()
    }

    fn sdiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_signed_div(lhs, rhs, "").into()
    }

    fn exactsdiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_exact_signed_div(lhs, rhs, "").into()
    }

    fn fdiv(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_float_value();
        let rhs = rhs.into_float_value();

        self.builder.build_float_div(lhs, rhs, "").into()
    }

    fn fdiv_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_float_value();
        let rhs = rhs.into_float_value();

        let value = self.builder.build_float_div(lhs, rhs, "");

        // @@Todo: set the `fast` metadata flag on this operation
        // value.as_instruction().map(|instruction| instruction.set_metadata(metadata,
        // kind_id)).into();
        value.into()
    }

    fn urem(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_unsigned_rem(lhs, rhs, "").into()
    }

    fn srem(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_signed_rem(lhs, rhs, "").into()
    }

    fn frem(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_float_value();
        let rhs = rhs.into_float_value();

        self.builder.build_float_rem(lhs, rhs, "").into()
    }

    fn frem_fast(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_float_value();
        let rhs = rhs.into_float_value();

        let value = self.builder.build_float_rem(lhs, rhs, "");

        // @@Todo: set the `fast` metadata flag on this operation
        // value.as_instruction().map(|instruction| instruction.set_metadata(metadata,
        // kind_id)).into();
        value.into()
    }

    fn fpow(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let ty = lhs.get_type().into_float_type();

        // For some reason there is no function to get the width
        // of a float type, so we have to use raw fn call yet again...
        let intrinsic = match { unsafe { LLVMGetTypeKind(ty.as_type_ref()) } } {
            llvm_sys::LLVMTypeKind::LLVMHalfTypeKind
            | llvm_sys::LLVMTypeKind::LLVMFloatTypeKind => "llvm.pow.f32",
            llvm_sys::LLVMTypeKind::LLVMDoubleTypeKind => "llvm.pow.f64",
            _ => unreachable!("unsupported float type for pow"),
        };

        let func = self.module.get_function(intrinsic).unwrap();
        self.call(func, &[lhs, rhs], None)
    }

    fn shl(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_left_shift(lhs, rhs, "").into()
    }

    fn lshr(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_right_shift(lhs, rhs, true, "").into()
    }

    fn ashr(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_right_shift(lhs, rhs, false, "").into()
    }

    fn unchecked_sadd(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_nsw_add(lhs, rhs, "").into()
    }

    fn unchecked_uadd(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_nuw_add(lhs, rhs, "").into()
    }

    fn unchecked_ssub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_nsw_sub(lhs, rhs, "").into()
    }

    fn unchecked_usub(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_nuw_sub(lhs, rhs, "").into()
    }

    fn unchecked_smul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_nsw_mul(lhs, rhs, "").into()
    }

    fn unchecked_umul(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_nuw_mul(lhs, rhs, "").into()
    }

    fn and(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_and(lhs, rhs, "").into()
    }

    fn or(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_or(lhs, rhs, "").into()
    }

    fn xor(&mut self, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_xor(lhs, rhs, "").into()
    }

    fn not(&mut self, v: Self::Value) -> Self::Value {
        let v = v.into_int_value();

        self.builder.build_not(v, "").into()
    }

    fn neg(&mut self, v: Self::Value) -> Self::Value {
        let v = v.into_int_value();

        self.builder.build_int_neg(v, "").into()
    }

    fn fneg(&mut self, v: Self::Value) -> Self::Value {
        let v = v.into_float_value();

        self.builder.build_float_neg(v, "").into()
    }

    fn checked_bin_op(
        &mut self,
        op: CheckedOp,
        ty: IrTyId,
        lhs: Self::Value,
        rhs: Self::Value,
    ) -> (Self::Value, Self::Value) {
        let ptr_width = self.ctx.settings().target().ptr_size();

        let int_ty = self.ir_ctx().map_ty(ty, |ty| match ty {
            IrTy::Int(ty @ SIntTy::ISize) => IntTy::Int(ty.normalise(ptr_width)),
            IrTy::Int(int_ty) => IntTy::Int(*int_ty),
            IrTy::UInt(ty @ UIntTy::USize) => IntTy::UInt(ty.normalise(ptr_width)),
            IrTy::UInt(int_ty) => IntTy::UInt(*int_ty),
            _ => unreachable!("tried to perform a checked operation on a non-integer type"),
        });

        // @@CodeSpeed: for unsigned subtraction we emit manually perform
        // the computation and check for overflow since it results in potentially
        // better optimisation...
        if op == CheckedOp::Sub && !int_ty.is_signed() {
            return (self.sub(lhs, rhs), self.icmp(IntComparisonKind::Ult, lhs, rhs));
        }

        let intrinsic_prefix = match (op, int_ty.is_signed()) {
            (CheckedOp::Add, true) => "llvm.sadd",
            (CheckedOp::Add, false) => "llvm.uadd",
            (CheckedOp::Sub, true) => "llvm.ssub",
            (CheckedOp::Sub, false) => "llvm.usub",
            (CheckedOp::Mul, true) => "llvm.smul",
            (CheckedOp::Mul, false) => "llvm.umul",
        };

        let size = int_ty.size(ptr_width).unwrap();
        let intrinsic_name = format!("{}.with.overflow.i{}", intrinsic_prefix, size.bits());

        let result = self.call_intrinsic(&intrinsic_name, &[lhs, rhs]);
        (self.extract_field_value(result, 0), self.extract_field_value(result, 1))
    }

    fn icmp(&mut self, op: IntComparisonKind, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let op = IntPredicateWrapper::from(op).0;
        let lhs = lhs.into_int_value();
        let rhs = rhs.into_int_value();

        self.builder.build_int_compare(op, lhs, rhs, "").into()
    }

    fn fcmp(&mut self, op: RealComparisonKind, lhs: Self::Value, rhs: Self::Value) -> Self::Value {
        let op = FloatPredicateWrapper::from(op).0;
        let lhs = lhs.into_float_value();
        let rhs = rhs.into_float_value();

        self.builder.build_float_compare(op, lhs, rhs, "").into()
    }

    fn truncate(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder.build_int_truncate(val.into_int_value(), dest_ty.into_int_type(), "").into()
    }

    fn sign_extend(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder.build_int_s_extend(val.into_int_value(), dest_ty.into_int_type(), "").into()
    }

    fn zero_extend(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder.build_int_z_extend(val.into_int_value(), dest_ty.into_int_type(), "").into()
    }

    fn fp_to_int_sat(
        &mut self,
        value: Self::Value,
        dest_ty: Self::Type,
        is_signed: bool,
    ) -> Self::Value {
        let src_ty = self.ty_of_value(value);

        // Deal with the source type potentially being a vector type.
        let (float_ty, int_ty, vec_width): (_, _, Option<usize>) = if src_ty.is_vector_type() {
            // @@Future: this isn't currently fired but when we work on supporting SIMD,
            // then we'll need to handle this case.
            unimplemented!()
        } else {
            (src_ty, dest_ty, None)
        };

        let float_width = self.float_width(float_ty);
        let int_width = self.int_width(int_ty);

        let instruction = if is_signed { "s" } else { "u" };
        let name = if let Some(vec_width) = vec_width {
            format!(
                "llvm.fpto{instruction}i.sat.v{vec_width}i{int_width}.v{vec_width}f{float_width}"
            )
        } else {
            format!("llvm.fpto{instruction}i.sat.i{int_width}.f{float_width}")
        };

        let fn_ty = self.type_function(&[src_ty], dest_ty);
        let func = self.declare_c_fn(&name, UnnamedAddress::None, fn_ty);

        self.call(func, &[value], None)
    }

    fn fp_to_ui(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder
            .build_float_to_unsigned_int(val.into_float_value(), dest_ty.into_int_type(), "")
            .into()
    }

    fn fp_to_si(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder
            .build_float_to_signed_int(val.into_float_value(), dest_ty.into_int_type(), "")
            .into()
    }

    fn ui_to_fp(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder
            .build_unsigned_int_to_float(val.into_int_value(), dest_ty.into_float_type(), "")
            .into()
    }

    fn si_to_fp(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder
            .build_signed_int_to_float(val.into_int_value(), dest_ty.into_float_type(), "")
            .into()
    }

    fn fp_truncate(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder.build_float_trunc(val.into_float_value(), dest_ty.into_float_type(), "").into()
    }

    fn fp_extend(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder.build_float_ext(val.into_float_value(), dest_ty.into_float_type(), "").into()
    }

    fn ptr_to_int(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder.build_ptr_to_int(val.into_pointer_value(), dest_ty.into_int_type(), "").into()
    }

    fn int_to_ptr(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder.build_int_to_ptr(val.into_int_value(), dest_ty.into_pointer_type(), ".").into()
    }

    fn bit_cast(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        let val: BasicValueEnum = val.try_into().unwrap();
        let ty: BasicTypeEnum = dest_ty.try_into().unwrap();

        self.builder.build_bitcast(val, ty, "").into()
    }

    fn int_cast(&mut self, val: Self::Value, dest_ty: Self::Type, is_signed: bool) -> Self::Value {
        self.builder
            .build_int_cast_sign_flag(val.into_int_value(), dest_ty.into_int_type(), is_signed, "")
            .into()
    }

    fn pointer_cast(&mut self, val: Self::Value, dest_ty: Self::Type) -> Self::Value {
        self.builder
            .build_pointer_cast(val.into_pointer_value(), dest_ty.into_pointer_type(), "")
            .into()
    }

    fn value_from_immediate(&mut self, value: Self::Value) -> Self::Value {
        // check if this is an `i1` value, i.e. a `bool`, and then if so
        // we zero extend the value into an `i8`
        if self.ctx.ty_of_value(value) == self.ctx.type_i1() {
            self.zero_extend(value, self.ctx.type_i8())
        } else {
            value
        }
    }

    fn to_immediate_scalar(&mut self, value: Self::Value, scalar_kind: Scalar) -> Self::Value {
        if scalar_kind.is_bool() {
            self.truncate(value, self.ctx.type_i1())
        } else {
            value
        }
    }

    fn alloca(&mut self, ty: Self::Type, alignment: Alignment) -> Self::Value {
        // @@Todo: do we need to start a new block here?

        let ty: BasicTypeEnum = ty.try_into().unwrap();
        let allocated_value = self.builder.build_alloca(ty, "");

        // we need to set the alignment of this value to the specified size.
        allocated_value
            .as_instruction()
            .map(|instruction| instruction.set_alignment(alignment.bytes() as u32));

        allocated_value.into()
    }

    fn byte_array_alloca(&mut self, len: Self::Value, alignment: Alignment) -> Self::Value {
        let ty: BasicTypeEnum = self.ctx.type_i8().try_into().unwrap();
        let allocated_value = self.builder.build_array_alloca(ty, len.into_int_value(), "");

        // we need to set the alignment of this value to the specified size.
        allocated_value
            .as_instruction()
            .map(|instruction| instruction.set_alignment(alignment.bytes() as u32));

        allocated_value.into()
    }

    fn write_operand_repeatedly(
        &mut self,
        operand: OperandRef<Self::Value>,
        count: usize,
        destination: PlaceRef<Self::Value>,
    ) {
        let zero = self.const_usize(0);
        let count = self.const_usize(count as u64);
        let start = destination.project_index(self, zero).value;
        let end = destination.project_index(self, count).value;

        // setup the blocks to write the operand to...
        let header_bb = self.append_sibling_block("repeat_loop_header");
        let body_bb = self.append_sibling_block("repeat_loop_body");
        let next_bb = self.append_sibling_block("repeat_loop_next");

        // jump to the header block
        self.branch(header_bb);

        let mut header_builder = Self::build(self.ctx, header_bb);

        let basic_value: BasicValueEnum = start.try_into().unwrap();
        let current: AnyValueEnum = header_builder
            .phi(
                self.ctx.ty_of_value(start),
                &[&basic_value as &dyn BasicValue],
                &[self.basic_block()],
            )
            .into();

        let keep_going = header_builder.icmp(IntComparisonKind::Ne, current, end);
        header_builder.conditional_branch(keep_going, body_bb, next_bb);

        let mut body_builder = Self::build(self.ctx, body_bb);

        let field_info = destination.info.field(self.ctx.layout_computer(), 0);
        let field_size = self.map_layout(field_info.layout, |layout| layout.size);

        let alignment = destination.alignment.restrict_to(field_size);

        // now we want to emit a `store` for the value we are writing
        operand.value.store(
            &mut body_builder,
            PlaceRef { value: current, extra: None, info: operand.info, alignment },
        );

        // Compute the "next" value...
        let ty = self.backend_ty_from_info(operand.info);
        let next: BasicValueEnum = body_builder
            .bounded_get_element_pointer(ty, current, &[self.const_usize(1)])
            .try_into()
            .unwrap();

        // and branch back to the header
        body_builder.branch(header_bb);
        header_builder.add_incoming_to_phi(current.into_phi_value(), next, body_bb);

        *self = Self::build(self.ctx, next_bb);
    }

    fn load(&mut self, ty: Self::Type, ptr: Self::Value, alignment: Alignment) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        let value = self.builder.build_load(ty, ptr.into_pointer_value(), "");

        // we need to set the alignment of this value to the specified size.
        value
            .as_instruction_value()
            .map(|instruction| instruction.set_alignment(alignment.bytes() as u32));

        value.into()
    }

    fn volatile_load(&mut self, ty: Self::Type, ptr: Self::Value) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        let value = self.builder.build_load(ty, ptr.into_pointer_value(), "");

        // we need to set that this data is volatile
        value.as_instruction_value().map(|instruction| instruction.set_volatile(true));

        value.into()
    }

    fn atomic_load(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        ordering: AtomicOrdering,
        size: Size,
    ) -> Self::Value {
        let ordering = AtomicOrderingWrapper::from(ordering).0;

        let ty: BasicTypeEnum = ty.try_into().unwrap();
        let value = self.builder.build_load(ty, ptr.into_pointer_value(), "");

        // we need to set that this data is volatile
        if let Some(instruction) = value.as_instruction_value() {
            instruction.set_atomic_ordering(ordering).unwrap();
            instruction.set_alignment(size.bytes() as u32).unwrap();
        }

        value.into()
    }

    fn load_operand(&mut self, place: PlaceRef<Self::Value>) -> OperandRef<Self::Value> {
        // If the operand is a zst, we return a `()` value
        self.ctx.map_layout(place.info.layout, |layout| {
            if layout.is_zst() {
                return OperandRef::new_zst(self, place.info);
            }

            let value = if layout.is_llvm_immediate() {
                let const_value = None;
                let ty = place.info.llvm_ty(self.ctx);

                // Check here if the need to load it in a as global value, i.e.
                // a constant...
                // @@PatchInkwell: need to patch inkwell to be able to check if things are
                // global variables, and constant.
                //
                // if let Some(global) = self.module.get_global(name) {
                //     ...
                // }

                // If this wasn't a global constant value, we'll just load it in
                // as a normal scalar.
                let value = const_value.unwrap_or_else(|| {
                    // Check if the type is pointing to a global constant value
                    let load_value = self.load(ty, place.value, place.alignment);

                    if let AbiRepresentation::Scalar(scalar) = layout.abi {
                        let instruction = instruction_from_any_value(load_value);

                        load_scalar_value_metadata(
                            self,
                            instruction,
                            scalar,
                            place.info,
                            Size::ZERO,
                        );
                    }

                    load_value
                });

                OperandValue::Immediate(self.to_immediate(value, place.info.layout))
            } else if let AbiRepresentation::Pair(scalar_a, scalar_b) = layout.abi {
                let b_offset = scalar_a.size(self).align_to(scalar_b.align(self).abi);
                let pair_ty = place.info.llvm_ty(self.ctx);

                // Utility closure to load one of the elements from the pair using
                // a `struct-gep`.
                let mut load = |index, scalar: Scalar, info, align, offset| {
                    let ptr =
                        self.structural_get_element_pointer(pair_ty, place.value, index as u64);
                    let ty = place.info.scalar_pair_element_llvm_ty(self.ctx, index, false);
                    let load_value = self.load(ty, ptr, align);

                    load_scalar_value_metadata(
                        self,
                        instruction_from_any_value(load_value),
                        scalar,
                        info,
                        offset,
                    );

                    self.to_immediate_scalar(load_value, scalar)
                };

                OperandValue::Pair(
                    load(0, scalar_a, place.info, place.alignment, Size::ZERO),
                    load(1, scalar_b, place.info, place.alignment.restrict_to(b_offset), b_offset),
                )
            } else {
                OperandValue::Ref(place.value, place.alignment)
            };

            OperandRef { value, info: place.info }
        })
    }

    fn store(&mut self, value: Self::Value, ptr: Self::Value, alignment: Alignment) -> Self::Value {
        self.store_with_flags(value, ptr, alignment, MemFlags::empty())
    }

    fn store_with_flags(
        &mut self,
        value: Self::Value,
        ptr: Self::Value,
        alignment: Alignment,
        flags: MemFlags,
    ) -> Self::Value {
        let operand: BasicValueEnum = value.try_into().unwrap();
        let store_value = self.builder.build_store(ptr.into_pointer_value(), operand);

        let alignment = if flags.contains(MemFlags::UN_ALIGNED) { 1 } else { alignment.bytes() };
        store_value.set_alignment(alignment as u32).unwrap();

        // We need to apply the specified flags
        if flags.contains(MemFlags::VOLATILE) {
            store_value.set_volatile(true).unwrap();
        }

        if flags.contains(MemFlags::NON_TEMPORAL) {
            // According to LLVM [1] building a `non-temporal` store must
            // *always* point to a metadata value of the integer 1.
            //
            // [1]: https://llvm.org/docs/LangRef.html#store-instruction
            let metadata: BasicMetadataValueEnum = self.ctx.const_i32(1).try_into().unwrap();
            let node = self.ctx.ll_ctx.metadata_node(&[metadata]);
            store_value.set_metadata(node, MetadataTypeKind::NonTemporal as u32).unwrap();
        }

        store_value.into()
    }

    fn atomic_store(
        &mut self,
        value: Self::Value,
        ptr: Self::Value,
        alignment: Alignment,
        ordering: AtomicOrdering,
    ) -> Self::Value {
        let operand: BasicValueEnum = value.try_into().unwrap();
        let store_value = self.builder.build_store(ptr.into_pointer_value(), operand);

        // we need to set the atomic ordering for the store.
        let ordering = AtomicOrderingWrapper::from(ordering).0;
        store_value.set_atomic_ordering(ordering).unwrap();

        let alignment = alignment.bytes();
        store_value.set_alignment(alignment as u32).unwrap();

        store_value.into()
    }

    fn get_element_pointer(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        indices: &[Self::Value],
    ) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        let indices = indices.iter().map(|i| i.into_int_value()).collect::<Vec<_>>();

        // ## Safety: If the `indices` are invalid or out of bounds, LLVM
        // is likely to segfault, which is noted by Inkwell and thus labelled
        // as `unsafe`.
        unsafe { self.builder.build_gep(ty, ptr.into_pointer_value(), &indices, "").into() }
    }

    fn bounded_get_element_pointer(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        indices: &[Self::Value],
    ) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        let indices = indices.iter().map(|i| i.into_int_value()).collect::<Vec<_>>();

        // ## Safety: If the `indices` are invalid or out of bounds, LLVM
        // is likely to segfault, which is noted by Inkwell and thus labelled
        // as `unsafe`.
        unsafe {
            self.builder.build_in_bounds_gep(ty, ptr.into_pointer_value(), &indices, "").into()
        }
    }

    fn structural_get_element_pointer(
        &mut self,
        ty: Self::Type,
        ptr: Self::Value,
        index: u64,
    ) -> Self::Value {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        let index = index as u32;

        self.builder.build_struct_gep(ty, ptr.into_pointer_value(), index, "").unwrap().into()
    }

    fn memcpy(
        &mut self,
        destination: (Self::Value, Alignment),
        source: (Self::Value, Alignment),
        size: Self::Value,
        flags: MemFlags,
    ) {
        // This should be handled by the `codegen_memcpy` function.
        debug_assert!(!flags.contains(MemFlags::NON_TEMPORAL), "non-temporal memcpy not supported");

        let size = self.int_cast(size, self.ctx.type_isize(), false).into_int_value();
        let is_volatile = flags.contains(MemFlags::VOLATILE);

        let (destination, destination_align) = destination;
        let (source, source_align) = source;

        // we need to cast the values into pointers...
        let destination = self.pointer_cast(destination, self.ctx.type_i8p()).into_pointer_value();
        let source = self.pointer_cast(source, self.ctx.type_i8p()).into_pointer_value();

        let value = self
            .builder
            .build_memcpy(
                destination,
                destination_align.bytes() as u32,
                source,
                source_align.bytes() as u32,
                size,
            )
            .unwrap();

        // Set the volatile flag if necessary
        if let Some(val) = value.as_instruction_value() {
            val.set_volatile(is_volatile).unwrap()
        }
    }

    fn memmove(
        &mut self,
        destination: (Self::Value, Alignment),
        source: (Self::Value, Alignment),
        size: Self::Value,
        flags: MemFlags,
    ) {
        // This should be handled by the `codegen_memcpy` function.
        debug_assert!(
            !flags.contains(MemFlags::NON_TEMPORAL),
            "non-temporal memmove not supported"
        );

        let size = self.int_cast(size, self.ctx.type_isize(), false).into_int_value();
        let is_volatile = flags.contains(MemFlags::VOLATILE);

        let (destination, destination_align) = destination;
        let (source, source_align) = source;

        // we need to cast the values into pointers...
        let destination = self.pointer_cast(destination, self.ctx.type_i8p()).into_pointer_value();
        let source = self.pointer_cast(source, self.ctx.type_i8p()).into_pointer_value();

        let value = self
            .builder
            .build_memmove(
                destination,
                destination_align.bytes() as u32,
                source,
                source_align.bytes() as u32,
                size,
            )
            .unwrap();

        // Set the volatile flag if necessary
        if let Some(val) = value.as_instruction_value() {
            val.set_volatile(is_volatile).unwrap()
        }
    }

    fn memset(
        &mut self,
        ptr: Self::Value,
        fill: Self::Value,
        size: Self::Value,
        alignment: Alignment,
        flags: MemFlags,
    ) {
        let is_volatile = flags.contains(MemFlags::VOLATILE);
        let ptr = self.pointer_cast(ptr, self.ctx.type_i8p()).into_pointer_value();

        let value = self
            .builder
            .build_memset(
                ptr,
                alignment.bytes() as u32,
                fill.into_int_value(),
                size.into_int_value(),
            )
            .unwrap();

        // Set the volatile flag if necessary
        if let Some(val) = value.as_instruction_value() {
            val.set_volatile(is_volatile).unwrap()
        }
    }

    fn select(
        &mut self,
        condition: Self::Value,
        then: Self::Value,
        otherwise: Self::Value,
    ) -> Self::Value {
        // @@Deal with potentially non-int values, we need to wrap IntMathValueEnum
        let value = condition.into_int_value();

        let then: BasicValueEnum = then.try_into().unwrap();
        let otherwise: BasicValueEnum = otherwise.try_into().unwrap();

        self.builder.build_select(value, then, otherwise, "").into()
    }

    fn lifetime_start(&mut self, ptr: Self::Value, size: Size) {
        self.emit_lifetime_marker("llvm.lifetime.start.p0i8", ptr, size)
    }

    fn lifetime_end(&mut self, ptr: Self::Value, size: Size) {
        self.emit_lifetime_marker("llvm.lifetime.end.p0i8", ptr, size)
    }

    fn add_range_metadata_to(&mut self, load_value: Self::Value, range: ValidScalarRange) {
        let ty = self.ctx.ty_of_value(load_value);

        let start: BasicMetadataValueEnum =
            self.ctx.const_uint_big(ty, range.start).try_into().unwrap();

        let end: BasicMetadataValueEnum =
            self.ctx.const_uint_big(ty, range.end.wrapping_add(1)).try_into().unwrap();

        let metadata = self.ctx.ll_ctx.metadata_node(&[start, end]);

        let value = instruction_from_any_value(load_value);
        value.set_metadata(metadata, MetadataTypeKind::Range as u32).unwrap();
    }

    fn extract_field_value(&mut self, value: Self::Value, field_index: usize) -> Self::Value {
        // @@Cleanup: maybe make this a standalone function?
        let value: AggregateValueEnum = match value {
            AnyValueEnum::StructValue(val) => AggregateValueEnum::StructValue(val),
            AnyValueEnum::ArrayValue(val) => AggregateValueEnum::ArrayValue(val),
            _ => unreachable!("attempt to extract field from non-aggregate value"),
        };

        self.builder.build_extract_value(value, field_index as u32, "").unwrap().into()
    }

    fn insert_field_value(
        &mut self,
        value: Self::Value,
        element: Self::Value,
        index: usize,
    ) -> Self::Value {
        // @@Cleanup: maybe make this a standalone function?
        let value: AggregateValueEnum = match value {
            AnyValueEnum::StructValue(val) => AggregateValueEnum::StructValue(val),
            AnyValueEnum::ArrayValue(val) => AggregateValueEnum::ArrayValue(val),
            _ => unreachable!("attempt to extract field from non-aggregate value"),
        };

        let element: BasicValueEnum = element.try_into().unwrap();
        self.builder
            .build_insert_value(value, element, index as u32, "")
            .unwrap()
            .as_any_value_enum()
    }
}

/// This will apply all of the stored metadata on the [Scalar] to
/// the value within the LLVM IR. Here, we emit information about the
/// [ValidScalarRange], alignment metadata and `non-null`ness.
fn load_scalar_value_metadata<'m>(
    builder: &mut Builder<'_, '_, 'm>,
    load: InstructionValue<'m>,
    scalar: Scalar,
    info: TyInfo,
    offset: Size,
) {
    // If the scalar is not a uninitialised value (`union`), then
    // we can specify that it will not be non-undef,
    if !scalar.is_union() {
        builder.set_no_undef(load);
    }

    match scalar.kind() {
        ScalarKind::Int { .. } => {
            // If the scalar has a particular value range, then we can emit
            // additional information to LLVM about this range using the `range!`
            // metadata.
            if !scalar.is_always_valid(builder.ctx) {
                // @@Dumbness: we're recasting back into any-value
                let value = load.as_any_value_enum();
                builder.add_range_metadata_to(value, scalar.valid_range(builder.ctx));
            }
        }
        ScalarKind::Float { .. } => {}
        ScalarKind::Pointer(_) => {
            // If we know that the pointer cannot be non-null,
            // then we emit this metadata.
            if scalar.valid_range(builder.ctx).contains(0) {
                builder.set_non_null(load);
            }

            // Compute the layout of the pointee_ty
            if let Some(pointee_info) =
                builder.layout_computer().compute_layout_info_of_pointee_at(info, offset)
            {
                if pointee_info.kind.is_some() {
                    builder.set_alignment(load, pointee_info.alignment);
                }
            }
        }
    }
}
