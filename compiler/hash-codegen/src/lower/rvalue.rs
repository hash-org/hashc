//! Module that deals with lowering [ir::RValue]s into
//! backend specific RValues.

use std::cmp::Ordering;

use hash_ir::{
    cast::{CastTy, IntCastKind},
    ir::{self, BinOp, RValue},
    ty::{self, COMMON_REPR_TYS, RefKind, ReprTyId, VariantIdx},
};
use hash_storage::store::statics::StoreId;

use super::{
    FnBuilder,
    locals::LocalRef,
    operands::{OperandRef, OperandValue},
    place::PlaceRef,
};
use crate::{
    common::{CheckedOp, IntComparisonKind, MemFlags, TypeKind},
    traits::{
        builder::BlockBuilderMethods, constants::ConstValueBuilderMethods, layout::LayoutMethods,
        ty::TypeBuilderMethods,
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
fn shift_mask_value<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>>(
    builder: &Builder,
    ty: Builder::Type,
    mask_ty: Builder::Type,
    invert: bool,
) -> Builder::Value {
    match builder.ty_kind(ty) {
        TypeKind::Integer => {
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
fn cast_shift_value<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>>(
    builder: &mut Builder,
    lhs: Builder::Value,
    rhs: Builder::Value,
) -> Builder::Value {
    let lhs_ty = builder.ty_of_value(lhs);
    let rhs_ty = builder.ty_of_value(rhs);

    let lhs_size = builder.int_width(lhs_ty);
    let rhs_size = builder.int_width(rhs_ty);

    // If the size of `lhs` is smaller than `rhs`, we need
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
fn apply_shift_mask<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>>(
    builder: &mut Builder,
    shift_value: Builder::Value,
) -> Builder::Value {
    let value_ty = builder.ty_of_value(shift_value);
    let mask = shift_mask_value(builder, value_ty, value_ty, false);
    builder.and(shift_value, mask)
}

/// This function will ensure that the operands to a `>>` (bitwise right-shift)
/// operator are always valid. This means that if the shifting value is greater
/// in size than the bit-width of the left-hand side operand, it needs
/// to be truncated, and similarly in the case where the shifting value is
/// smaller than the bit-width of the left-hand side operand, it needs to be
/// zero extended.
fn build_unchecked_rshift<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>>(
    builder: &mut Builder,
    ty: ReprTyId,
    lhs: Builder::Value,
    rhs: Builder::Value,
) -> Builder::Value {
    let rhs = cast_shift_value(builder, lhs, rhs);
    let rhs = apply_shift_mask(builder, rhs);

    if ty.borrow().is_signed() {
        // Arithmetic right shift
        builder.ashr(lhs, rhs)
    } else {
        // Logical right shift
        builder.lshr(lhs, rhs)
    }
}

fn build_unchecked_lshift<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>>(
    builder: &mut Builder,
    lhs: Builder::Value,
    rhs: Builder::Value,
) -> Builder::Value {
    let rhs = cast_shift_value(builder, lhs, rhs);
    let rhs = apply_shift_mask(builder, rhs);
    builder.shl(lhs, rhs)
}

impl<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> FnBuilder<'a, 'b, Builder> {
    /// Emit code for the given [ir::RValue] and store the result in the
    /// given [PlaceRef].
    pub fn codegen_rvalue(
        &mut self,
        builder: &mut Builder,
        destination: PlaceRef<Builder::Value>,
        rvalue: &ir::RValue,
    ) {
        match rvalue {
            ir::RValue::Use(operand) => {
                let operand = self.codegen_operand(builder, operand);
                operand.value.store(builder, destination);
            }
            ir::RValue::Repeat(op, repeat) => {
                let op = self.codegen_operand(builder, op);

                // We don't write anything into the destination if it is a ZST... i.e. being
                // ignored!
                if destination.info.is_zst() {
                    return;
                }

                // Optimisation for immediate, we can use llvm.memset.p0i8.* to
                // initialise the memory.
                if let OperandValue::Immediate(val) = op.value {
                    let zero = builder.const_usize(0);
                    let start = destination.project_index(builder, zero).value;
                    let size = builder.const_usize(destination.info.size().bytes());

                    // If it is zero, we just fill the array with zeroes...
                    if self.ctx.const_to_optional_u128(val, false) == Some(0) {
                        let fill = self.ctx.const_u8(0);
                        builder.memset(start, fill, size, destination.alignment, MemFlags::empty());
                        return;
                    }

                    // If the type is the size of a `i8`, we just memset it with the value...
                    let v = builder.value_from_immediate(val);
                    if self.ctx.ty_of_value(v) == self.ctx.type_i8() {
                        builder.memset(start, v, size, destination.alignment, MemFlags::empty());
                        return;
                    }
                }

                // Slow-path: we actually need to generate code to write the value into the
                // array...
                builder.write_operand_repeatedly(op, *repeat, destination)
            }
            ir::RValue::Aggregate(kind, operands) => {
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
                    let is_zst = operand.info.layout.borrow().is_zst();

                    // We don't need to do anything for ZSTs...
                    if !is_zst {
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

    /// Compute the type of an [RValue].
    pub fn ty_of_rvalue(&self, value: &RValue) -> ReprTyId {
        value.ty(&self.body.aux())
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
                let info = builder.layout_of(ty);
                let (size, alignment) =
                    info.layout.map(|layout| (layout.size.bytes(), layout.alignment.abi.bytes()));

                let value_bytes = match op {
                    ir::ConstOp::SizeOf => size,
                    ir::ConstOp::AlignOf => alignment,
                };
                let value = builder.ctx().const_usize(value_bytes);

                OperandRef {
                    value: OperandValue::Immediate(value),
                    info: builder.layout_of(COMMON_REPR_TYS.usize),
                }
            }
            ir::RValue::UnaryOp(operator, ref operand) => {
                let operand = self.codegen_operand(builder, operand);
                let value = operand.immediate_value();

                let value = match operator {
                    ir::UnOp::BitNot | ir::UnOp::Not => builder.not(value),
                    ir::UnOp::Neg => {
                        // check if the underlying value is a floating point...
                        if self.ty_of_rvalue(rvalue).borrow().is_float() {
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
                    (
                        OperandValue::Pair(lhs_addr, lhs_extra),
                        OperandValue::Pair(rhs_addr, rhs_extra),
                    ) => self.codegen_pair_binop(
                        builder, operator, lhs_addr, lhs_extra, rhs_addr, rhs_extra,
                    ),
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
                    info: builder.layout_of(operator.ty(lhs.info.ty, rhs.info.ty)),
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
                OperandRef { value: result, info: builder.layout_of(self.ty_of_rvalue(rvalue)) }
            }
            ir::RValue::Cast(_, op, ir_ty) => {
                let operand = self.codegen_operand(builder, &op);
                let cast_ty = builder.layout_of(ir_ty);

                let out_ty = builder.immediate_backend_ty(cast_ty);

                // If the operand is a ZST, then we just return the new
                // operand as an undefined value of the cast_ty
                if operand.info.is_uninhabited() {
                    let value = OperandValue::Immediate(builder.const_undef(out_ty));
                    return OperandRef { value, info: cast_ty };
                }

                let in_cast_ty =
                    CastTy::from_ty(operand.info.ty).expect("expected cast-able type for cast");
                let out_cast_ty =
                    CastTy::from_ty(cast_ty.ty).expect("expected cast-able type for cast");

                let in_ty = builder.immediate_backend_ty(operand.info);
                let value = operand.immediate_value();

                let new_value = match (in_cast_ty, out_cast_ty) {
                    (CastTy::Int(in_ty), CastTy::Int(_)) => {
                        builder.int_cast(value, out_ty, in_ty.is_signed())
                    }
                    (CastTy::Ref, CastTy::Int(IntCastKind::UInt)) => {
                        builder.ptr_to_int(value, out_ty)
                    }
                    (CastTy::Int(IntCastKind::UInt), CastTy::Ref) => {
                        builder.int_to_ptr(value, out_ty)
                    }
                    (CastTy::Int(in_ty), CastTy::Float) => {
                        if in_ty.is_signed() {
                            builder.si_to_fp(value, out_ty)
                        } else {
                            builder.ui_to_fp(value, out_ty)
                        }
                    }
                    (CastTy::Float, CastTy::Int(IntCastKind::Int)) => {
                        builder.float_to_int_cast(value, out_ty, true)
                    }
                    (CastTy::Float, CastTy::Int(_)) => {
                        builder.float_to_int_cast(value, out_ty, false)
                    }
                    (CastTy::Float, CastTy::Float) => {
                        let src_size = builder.float_width(in_ty);
                        let dest_size = builder.float_width(out_ty);

                        match src_size.cmp(&dest_size) {
                            Ordering::Less => builder.fp_extend(value, out_ty),
                            Ordering::Greater => builder.fp_truncate(value, out_ty),
                            Ordering::Equal => value,
                        }
                    }
                    _ => {
                        unreachable!("invalid cast from `{:?}` to `{:?}`", in_cast_ty, out_cast_ty)
                    }
                };

                let value = OperandValue::Immediate(new_value);
                OperandRef { value, info: cast_ty }
            }
            ir::RValue::Repeat(_, _) | ir::RValue::Aggregate(_, _) => {
                // This is only called if the aggregate value is a ZST, so we just
                // create a new ZST operand...
                OperandRef::zst(builder.layout_of(self.ty_of_rvalue(rvalue)))
            }
            ir::RValue::Len(place) => {
                let size = self.evaluate_array_len(builder, place);

                OperandRef {
                    value: OperandValue::Immediate(size),
                    info: builder.layout_of(COMMON_REPR_TYS.usize),
                }
            }
            ir::RValue::Ref(_, place, kind) => {
                match kind {
                    RefKind::Normal | RefKind::Raw => {
                        let ty = self.ty_of_rvalue(rvalue);
                        let place = self.codegen_place(builder, place);

                        // When slices are passed, we might need to use
                        // OperandValue::Pair (to pass the actual pointer and then
                        // the length of the slice as an implicit value using `extra`)
                        let value = if !self.ctx.ty_has_hidden_metadata(ty) {
                            OperandValue::Immediate(place.value)
                        } else {
                            OperandValue::Pair(place.value, place.extra.unwrap())
                        };

                        OperandRef { value, info: builder.layout_of(ty) }
                    }

                    // @@Pointers: decide more clearly on what this means, and
                    // when they are used/rules, etc.
                    RefKind::Rc => unimplemented!(),
                }
            }
            ir::RValue::Discriminant(place) => {
                let discriminant_ty = self.ty_of_rvalue(rvalue);
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
        ty: ReprTyId,
    ) -> Builder::Value {
        let is_float = ty.borrow().is_float();
        let is_signed = ty.borrow().is_signed();

        match operator {
            ir::BinOp::Add => {
                if is_float {
                    builder.fadd(lhs_value, rhs_value)
                } else {
                    builder.add(lhs_value, rhs_value)
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
    /// cases additional code is generated to deal with unforeseen
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
        ty: ReprTyId,
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
                    builder.checked_bin_op(checked_operator, ty, lhs_value, rhs_value);

                (value, overflow)
            }
            BinOp::Shl | BinOp::Shr => {
                let lhs_ty = builder.ty_of_value(lhs_value);
                let rhs_ty = builder.ty_of_value(rhs_value);

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

    /// Emit code for a [ir::BinOp] which is being applied to two
    /// [OperandValue::Pair]s. This is usually for `SizedPointer`s, and or
    /// strings (which is the same representation).
    fn codegen_pair_binop(
        &mut self,
        builder: &mut Builder,
        operator: ir::BinOp,
        lhs_addr: Builder::Value,
        lhs_extra: Builder::Value,
        rhs_addr: Builder::Value,
        rhs_extra: Builder::Value,
    ) -> Builder::Value {
        match operator {
            BinOp::Eq => {
                // We emit the following:
                //
                // lhs.0 == rhs.0 && lhs.1 == rhs.1

                let lhs = builder.icmp(IntComparisonKind::Eq, lhs_addr, rhs_addr);
                let rhs = builder.icmp(IntComparisonKind::Eq, lhs_extra, rhs_extra);
                builder.and(lhs, rhs)
            }
            BinOp::Neq => {
                // We emit the following:
                //
                // lhs.0 != rhs.0 || lhs.1 != rhs.1

                let lhs = builder.icmp(IntComparisonKind::Ne, lhs_addr, rhs_addr);
                let rhs = builder.icmp(IntComparisonKind::Ne, lhs_extra, rhs_extra);
                builder.or(lhs, rhs)
            }
            BinOp::Gt | BinOp::GtEq | BinOp::Lt | BinOp::LtEq => {
                let (op, strict_op) = match operator {
                    BinOp::Lt => (IntComparisonKind::Ult, IntComparisonKind::Ult),
                    BinOp::LtEq => (IntComparisonKind::Ule, IntComparisonKind::Ult),
                    BinOp::Gt => (IntComparisonKind::Ugt, IntComparisonKind::Ugt),
                    BinOp::GtEq => (IntComparisonKind::Uge, IntComparisonKind::Ugt),
                    _ => unreachable!(),
                };

                // We generate the following expression:
                //
                // lhs.0 <STRICT_OP> lhs.1 || (lhs.0 == rhs.0 && lhs.1 <OP> rhs.1)

                let lhs = builder.icmp(strict_op, lhs_addr, rhs_addr);
                let and_lhs = builder.icmp(op, lhs_extra, rhs_extra);
                let and_rhs = builder.icmp(IntComparisonKind::Eq, lhs_addr, rhs_addr);
                let rhs = builder.and(and_lhs, and_rhs);
                builder.or(lhs, rhs)
            }
            op => panic!("unexpected binary operator `{}` on scalar pairs", op),
        }
    }

    /// Check whether the given [ir::RValue] will create an
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
            | ir::RValue::Cast(_, _, _)
            | ir::RValue::Discriminant(_) => true,
            ir::RValue::Repeat(_, _) | ir::RValue::Aggregate(_, _) => {
                // check if the type is a ZST, and if so this satisfies the
                // case that the rvalue creates an operand...
                let ty = self.ty_of_rvalue(rvalue);
                self.ctx.layout_of(ty).is_zst()
            }
        }
    }

    /// Compute the length of a given array stored at the provided
    /// [Place]. This computes the value and returns a [`Builder::Value`]
    /// from it.
    fn evaluate_array_len(&mut self, builder: &mut Builder, place: ir::Place) -> Builder::Value {
        if let Some(local) = place.as_local() {
            if let LocalRef::Operand(Some(op)) = self.locals[local] {
                let size = op.info.ty.map(|ty| {
                    if let ty::ReprTy::Array { length: size, .. } = ty { Some(*size) } else { None }
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
