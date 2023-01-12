//! Module that deals with lowering [ir::RValue]s into
//! backend specific RValues.

use hash_ir::{
    ir::{self, BinOp},
    ty::{self, IrTyId, VariantIdx},
};
use hash_utils::store::Store;

use super::{
    locals::LocalRef,
    operands::{OperandRef, OperandValue},
    place::PlaceRef,
    FnBuilder,
};
use crate::{
    common::{CheckedOp, IntComparisonKind, TypeKind},
    traits::{
        builder::BlockBuilderMethods, constants::BuildConstValueMethods, ctx::HasCtxMethods,
        layout::LayoutMethods, ty::BuildTypeMethods,
    },
};

/// This computes a bit-shift mask for the provided `mask_ty`. This function
/// is used to compute the mask for the `shl` and `shr` operations. In
/// principle, this is used to make bit-shift operations all "safe". In
/// particular, this deals with the case where the shift amount is greater than
/// the bit-width of the type. In this event, we take the bit-width of the type,
/// and subtract 1. This is because it is only valid to shift an integer type by
/// `bits - 1` places, e.g. shifting an `i8` by 7 places is valid, but shifting
/// it by 8 places is not. So, the mask is computed, and then applied onto the
/// shifting value in order to check whether a shift overflow has occurred.
fn shift_mask_value<'b, Builder: BlockBuilderMethods<'b>>(
    builder: &mut Builder,
    ty: Builder::Type,
    mask_ty: Builder::Type,
    invert: bool,
) -> Builder::Value {
    match builder.kind_of_type(ty) {
        TypeKind::IntegerTy => {
            let bits = builder.int_width(ty) - 1;

            if invert {
                builder.const_int(mask_ty, !bits as i64)
            } else {
                builder.const_uint(mask_ty, bits)
            }
        }
        _ => unreachable!("cannot apply bit shift mask on non integer type"),
    }
}

/// This adjusts the `shift_value` to the size of `lhs`. This is
/// necessary because the size of `lhs` and `rhs` may not be the
/// same. For example, `i8` and `i32` are not the same size, so
/// we need to adjust the size of `rhs` to the size of `lhs`.
///
/// This is done by either truncating or zero extending the
/// `shift_value` to the size of `lhs`.
fn cast_shift_value<'b, Builder: BlockBuilderMethods<'b>>(
    builder: &mut Builder,
    lhs: Builder::Value,
    rhs: Builder::Value,
) -> Builder::Value {
    let lhs_ty = builder.type_of_value(lhs);
    let rhs_ty = builder.type_of_value(rhs);

    let lhs_size = builder.int_width(lhs_ty);
    let rhs_size = builder.int_width(rhs_ty);

    // If the size of `lhs` is smallar than `rhs`, we need
    // to truncate `rhs` to the size of `lhs`.
    match lhs_size.cmp(&rhs_size) {
        std::cmp::Ordering::Less => builder.truncate(rhs, lhs_ty),
        std::cmp::Ordering::Equal => rhs,
        std::cmp::Ordering::Greater => {
            // If the size is larger than `rhs`, we zero extended
            // the to the size of `lhs`
            builder.zero_extend(rhs, lhs_ty)
        }
    }
}

/// This function computes the appropriate shifting mask for
/// the `shift_value` and applies it the value for use. This
/// is to ensure that the shift value is always valid.
///
/// This is equivalent of what x86 machine instructions like `sarl`
/// perform. More information at <https://en.wikibooks.org/wiki/X86_Assembly/Shift_and_Rotate>.
fn apply_shift_mask<'b, Builder: BlockBuilderMethods<'b>>(
    builder: &mut Builder,
    shift_value: Builder::Value,
) -> Builder::Value {
    let value_ty = builder.type_of_value(shift_value);
    let mask = shift_mask_value(builder, value_ty, value_ty, false);
    builder.and(shift_value, mask)
}

/// This function will ensure that the operands to a `>>` (bitwise right-shift)
/// operator are always valid. This means that if the shifting value is greater
/// in size than the bit-width of the left-hand side operand, it needs
/// to be truncated, and similarly in the case where the shifting value is
/// smaller than the bit-width of the left-hand side operand, it needs to be
/// zero extended.
fn build_unchecked_rshift<'b, Builder: BlockBuilderMethods<'b>>(
    builder: &mut Builder,
    ty: IrTyId,
    lhs: Builder::Value,
    rhs: Builder::Value,
) -> Builder::Value {
    let rhs = cast_shift_value(builder, lhs, rhs);
    let rhs = apply_shift_mask(builder, rhs);
    let is_signed = builder.ctx().ir_ctx().tys().map_fast(ty, |ty| ty.is_signed());

    if is_signed {
        // Arithemetic right shift
        builder.ashr(lhs, rhs)
    } else {
        // Logical right shift
        builder.lshr(lhs, rhs)
    }
}

fn build_unchecked_lshift<'b, Builder: BlockBuilderMethods<'b>>(
    builder: &mut Builder,
    lhs: Builder::Value,
    rhs: Builder::Value,
) -> Builder::Value {
    let rhs = cast_shift_value(builder, lhs, rhs);
    let rhs = apply_shift_mask(builder, rhs);
    builder.shl(lhs, rhs)
}

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {
    /// Emit code for the given [ir::RValue] and store the result in the
    /// given [PlaceRef].
    pub fn codegen_rvalue(
        &mut self,
        builder: &mut Builder,
        destination: PlaceRef<Builder::Value>,
        rvalue: &ir::RValue,
    ) {
        // @@Todo: introduce casting, and deal with the code generation
        match *rvalue {
            // specifics here.
            ir::RValue::Use(ref operand) => {
                let operand = self.codegen_operand(builder, operand);
                operand.value.store(builder, destination);
            }
            ir::RValue::Aggregate(ref kind, ref operands) => {
                let destination = match *kind {
                    ir::AggregateKind::Enum(_, variant) => {
                        destination.codegen_set_discriminant(builder, variant);
                        destination.project_downcast(builder, variant)
                    }
                    ir::AggregateKind::Struct(_) => {
                        destination.codegen_set_discriminant(builder, VariantIdx::new(0));
                        destination
                    }
                    _ => destination,
                };

                for (i, operand) in operands.iter().enumerate() {
                    let operand = self.codegen_operand(builder, operand);
                    let layout = builder.layout_info(operand.info.layout);

                    // We don't need to do anything for ZSTs...
                    if !layout.is_zst() {
                        // Create the field place reference, and then store the
                        // value in the operand.
                        let field = if let ir::AggregateKind::Array(_) = *kind {
                            let value_index = builder.const_usize(i as u64);
                            destination.project_index(builder, value_index)
                        } else {
                            destination.project_field(builder, i)
                        };

                        operand.value.store(builder, field);
                    }
                }
            }
            _ => {
                debug_assert!(self.rvalue_creates_operand(rvalue));

                let temp = self.codegen_rvalue_operand(builder, rvalue);
                temp.value.store(builder, destination);
            }
        }
    }

    /// Emit code for a [ir::RValue] that will return an [OperandRef].
    pub fn codegen_rvalue_operand(
        &mut self,
        builder: &mut Builder,
        rvalue: &ir::RValue,
    ) -> OperandRef<Builder::Value> {
        match *rvalue {
            ir::RValue::Use(operand) => self.codegen_operand(builder, &operand),
            ir::RValue::ConstOp(op, ty) => {
                // compute the layout of the type, and then depending
                // on the operation it then emits the size or the
                // alignment.
                let info = builder.layout_of_id(ty);
                let layout = builder.layout_info(info.layout);

                let value_bytes = match op {
                    ir::ConstOp::SizeOf => layout.size.bytes(),
                    ir::ConstOp::AlignOf => layout.alignment.abi.bytes(),
                };
                let value = builder.ctx().const_usize(value_bytes);

                OperandRef {
                    value: OperandValue::Immediate(value),
                    info: builder.layout_of_id(self.ctx.ir_ctx().tys().common_tys.usize),
                }
            }
            ir::RValue::UnaryOp(operator, ref operand) => {
                let operand = self.codegen_operand(builder, operand);
                let value = operand.immediate_value();

                let value = match operator {
                    ir::UnaryOp::BitNot | ir::UnaryOp::Not => builder.not(value),
                    ir::UnaryOp::Neg => {
                        // check if the underlying value is a floating point...
                        let ty = rvalue.ty(self.ctx.ir_ctx());

                        if ty.is_float() {
                            builder.fneg(value)
                        } else {
                            builder.neg(value)
                        }
                    }
                };

                OperandRef { value: OperandValue::Immediate(value), info: operand.info }
            }
            ir::RValue::BinaryOp(operator, box (ref lhs, ref rhs)) => {
                let lhs = self.codegen_operand(builder, lhs);
                let rhs = self.codegen_operand(builder, rhs);

                let result = match (lhs.value, rhs.value) {
                    // @@Future: Here, we should deal with non-scalar binary operations.
                    // This occurs when a binary operator is implemented on a non-primitive
                    // type meaning that there is an implicit function dispatch to compute
                    // the resultant value.
                    (OperandValue::Pair(_, _), OperandValue::Pair(_, _)) => {
                        unimplemented!()
                    }
                    (OperandValue::Immediate(lhs_value), OperandValue::Immediate(rhs_value)) => {
                        self.codegen_scalar_binop(
                            builder,
                            operator,
                            lhs_value,
                            rhs_value,
                            lhs.info.ty,
                        )
                    }
                    _ => unreachable!(),
                };

                OperandRef {
                    value: OperandValue::Immediate(result),
                    info: builder.layout_of_id(operator.ty(
                        self.ctx.ir_ctx(),
                        lhs.info.ty,
                        rhs.info.ty,
                    )),
                }
            }
            ir::RValue::CheckedBinaryOp(operator, box (ref lhs, ref rhs)) => {
                let lhs = self.codegen_operand(builder, lhs);
                let rhs = self.codegen_operand(builder, rhs);

                let result = self.codegen_checked_scalar_binop(
                    builder,
                    operator,
                    lhs.immediate_value(),
                    rhs.immediate_value(),
                    lhs.info.ty,
                );

                // This yields the operand ty as `(<lhs_ty>, bool)`.
                let operand_ty = self.ctx.ir_ctx().tys().create(rvalue.ty(self.ctx.ir_ctx()));

                OperandRef { value: result, info: builder.layout_of_id(operand_ty) }
            }
            ir::RValue::Aggregate(_, _) => {
                // This is only called if the aggregate value is a ZST, so we just
                // create a new ZST operand...
                let info = builder.layout_of(rvalue.ty(self.ctx.ir_ctx()));
                OperandRef::new_zst(builder, info)
            }
            ir::RValue::Len(place) => {
                let size = self.evaluate_array_len(builder, place);

                OperandRef {
                    value: OperandValue::Immediate(size),
                    info: builder.layout_of_id(self.ctx.ir_ctx().tys().common_tys.usize),
                }
            }
            ir::RValue::Ref(_, place, kind) => {
                match kind {
                    ir::AddressMode::Raw => {
                        let ty = rvalue.ty(self.ctx.ir_ctx());
                        let place = self.codegen_place(builder, place);

                        // @@Todo: when slices are passed, we might need to use
                        // OperandValue::Pair (to pass the actual pointer and then
                        // the length of the slice as an implicit value using `extra`)
                        OperandRef {
                            value: OperandValue::Immediate(place.value),
                            info: builder.layout_of(ty),
                        }
                    }

                    // @@Pointers: decide more clearly on what this means, and
                    // when they are used/rules, etc.
                    ir::AddressMode::Smart => unimplemented!(),
                }
            }
            ir::RValue::Discriminant(place) => {
                let discriminant_ty = rvalue.ty(self.ctx.ir_ctx());
                let discriminant = self
                    .codegen_place(builder, place)
                    .codegen_get_discriminant(builder, discriminant_ty);

                OperandRef {
                    value: OperandValue::Immediate(discriminant),
                    info: builder.layout_of(discriminant_ty),
                }
            }
        }
    }

    /// Generate code for a trivial binary operation involving scalar-like
    /// operands.
    fn codegen_scalar_binop(
        &mut self,
        builder: &mut Builder,
        operator: ir::BinOp,
        lhs_value: Builder::Value,
        rhs_value: Builder::Value,
        ty: IrTyId,
    ) -> Builder::Value {
        let (is_float, is_signed) =
            self.ctx.ir_ctx().tys().map_fast(ty, |ty| (ty.is_float(), ty.is_signed()));

        match operator {
            ir::BinOp::Add => {
                if is_float {
                    builder.fsub(lhs_value, rhs_value)
                } else {
                    builder.sub(lhs_value, rhs_value)
                }
            }
            ir::BinOp::Sub => {
                if is_float {
                    builder.fsub(lhs_value, rhs_value)
                } else {
                    builder.sub(lhs_value, rhs_value)
                }
            }
            ir::BinOp::Mul => {
                if is_float {
                    builder.fmul(lhs_value, rhs_value)
                } else {
                    builder.mul(lhs_value, rhs_value)
                }
            }
            ir::BinOp::Div => {
                if is_float {
                    builder.fdiv(lhs_value, rhs_value)
                } else if is_signed {
                    builder.sdiv(lhs_value, rhs_value)
                } else {
                    builder.udiv(lhs_value, rhs_value)
                }
            }
            ir::BinOp::Mod => {
                if is_float {
                    builder.frem(lhs_value, rhs_value)
                } else if is_signed {
                    builder.srem(lhs_value, rhs_value)
                } else {
                    builder.urem(lhs_value, rhs_value)
                }
            }
            ir::BinOp::Exp => {
                if is_float {
                    builder.fpow(lhs_value, rhs_value)
                } else {
                    // Integer scalars don't support, @@Todo: maybe we can use:
                    //
                    // https://llvm.org/docs/LangRef.html#llvm-experimental-constrained-powi-intrinsic
                    unreachable!("`**` for integer operands is illegal")
                }
            }

            ir::BinOp::BitOr => builder.or(lhs_value, rhs_value),
            ir::BinOp::BitAnd => builder.and(lhs_value, rhs_value),
            ir::BinOp::BitXor => builder.xor(lhs_value, rhs_value),

            ir::BinOp::Shr => build_unchecked_rshift(builder, ty, lhs_value, rhs_value),
            ir::BinOp::Shl => build_unchecked_lshift(builder, lhs_value, rhs_value),

            ir::BinOp::Eq
            | ir::BinOp::Neq
            | ir::BinOp::Gt
            | ir::BinOp::GtEq
            | ir::BinOp::Lt
            | ir::BinOp::LtEq => {
                if is_float {
                    builder.fcmp(
                        operator.try_into().expect(
                            "cannot convert `BinOp` into floating-point comparison operator",
                        ),
                        lhs_value,
                        rhs_value,
                    )
                } else {
                    builder.icmp(
                        IntComparisonKind::from_bin_op(operator, is_signed),
                        lhs_value,
                        rhs_value,
                    )
                }
            }
        }
    }

    /// Code generate a check binary operation on scalar-like
    /// operands. For the most part, this will emit the intrinsics
    /// that are used for "checked" operations, but in some other
    /// cases additional code is generated to deal with unforseen
    /// U.B. when it comes to some operators (specifically bit shifts).
    ///
    /// N.B. it is an invariant to pass a [ir::BinOp] that is not
    /// checkable.
    fn codegen_checked_scalar_binop(
        &mut self,
        builder: &mut Builder,
        operator: ir::BinOp,
        lhs_value: Builder::Value,
        rhs_value: Builder::Value,
        ty: IrTyId,
    ) -> OperandValue<Builder::Value> {
        let (value, overflow) = match operator {
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let checked_operator = match operator {
                    BinOp::Add => CheckedOp::Add,
                    BinOp::Sub => CheckedOp::Sub,
                    BinOp::Mul => CheckedOp::Mul,
                    _ => unreachable!(),
                };

                let (value, overflow) =
                    builder.checked_bin_op(checked_operator, lhs_value, rhs_value);

                (value, overflow)
            }
            BinOp::Shl | BinOp::Shr => {
                let lhs_ty = builder.type_of_value(lhs_value);
                let rhs_ty = builder.type_of_value(rhs_value);

                let invert_mask = shift_mask_value(builder, lhs_ty, rhs_ty, true);
                let outer_bits = builder.and(rhs_value, invert_mask);

                // If the outer_bits don't equal to zero, then an overflow will occur
                // since we know that if the result is non-zero, then it is greater
                // than the maximum legal bit-shift value.
                let overflow =
                    builder.icmp(IntComparisonKind::Ne, outer_bits, builder.const_null(rhs_ty));
                let value = self.codegen_scalar_binop(builder, operator, lhs_value, rhs_value, ty);

                (value, overflow)
            }
            _ => unreachable!("operator `{operator}` is not checkable"),
        };

        OperandValue::Pair(value, overflow)
    }

    /// Check whether the given [RValue] will create an
    /// operand or not.
    pub fn rvalue_creates_operand(&self, rvalue: &ir::RValue) -> bool {
        match *rvalue {
            ir::RValue::Use(_)
            | ir::RValue::ConstOp(_, _)
            | ir::RValue::UnaryOp(_, _)
            | ir::RValue::BinaryOp(_, _)
            | ir::RValue::CheckedBinaryOp(_, _)
            | ir::RValue::Len(_)
            | ir::RValue::Ref(_, _, _)
            | ir::RValue::Discriminant(_) => true,
            ir::RValue::Aggregate(_, _) => {
                let ty = rvalue.ty(self.ctx.ir_ctx());

                // check if the type is a ZST, and if so this satisfies the
                // case that the rvalue creates an operand...
                self.ctx.layout_of(ty).is_zst(self.ctx.layout_ctx())
            }
        }
    }

    /// Compute the length of a given array stored at the provided
    /// [Place]. This computes the value and returns a [`Builder::Value`]
    /// from it.
    fn evaluate_array_len(&mut self, builder: &mut Builder, place: ir::Place) -> Builder::Value {
        if let Some(local) = place.as_local() {
            if let LocalRef::Operand(Some(op)) = self.locals[local] {
                let size = self.ctx.ir_ctx().tys().map_fast(op.info.ty, |ty| {
                    if let ty::IrTy::Array { size, .. } = ty {
                        Some(*size)
                    } else {
                        None
                    }
                });

                if let Some(size) = size {
                    return builder.const_usize(size as u64);
                }
            }
        }

        // If this is a reference to a place, we codegen the place
        // and the compute the `length` using the method available
        // on PlaceRef
        let value = self.codegen_place(builder, place);
        value.len(builder)
    }
}
