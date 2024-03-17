//! Module that hosts all of the logic that deals with emitting
//! code and resolving references to intrinsic function calls.

use hash_abi::ArgAbi;
use hash_ir::{intrinsics::Intrinsic, lang_items::LangItem, ty::InstanceId};
use hash_repr::TyInfo;
use hash_target::abi;

use super::{operands::OperandRef, place::PlaceRef, FnBuilder};
use crate::{
    lower::operands::{OperandValue, OperandValueKind},
    traits::{
        builder::BlockBuilderMethods, misc::MiscBuilderMethods, ty::TypeBuilderMethods,
        HasCtxMethods,
    },
};

impl<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> FnBuilder<'a, 'b, Builder> {
    /// Resolve a reference to an [LangItem].
    pub(super) fn resolve_lang_item(
        &mut self,
        builder: &Builder,
        item: LangItem,
    ) -> (InstanceId, Builder::Value) {
        let instance = self.ctx.ir_ctx().lang_items().get(item).unwrap();
        (instance, builder.get_fn_ptr(instance))
    }

    /// Function that handles generating code for the defined language
    /// intrinsics.
    pub(super) fn codegen_intrinsic(
        &mut self,
        builder: &mut Builder,
        intrinsic: Intrinsic,
        ret_abi: &ArgAbi,
        args: &[OperandRef<Builder::Value>],
        result: Builder::Value,
    ) {
        let result = PlaceRef::new(result, ret_abi.info);

        let value = match intrinsic {
            Intrinsic::Abort => {
                builder.codegen_abort_intrinsic();
                return;
            }
            Intrinsic::Transmute => {
                // This is dealt with before it reaches here.
                return;
            }
            Intrinsic::PtrOffset => {
                let ty = args[0].info;

                let ptr = args[0].immediate_value();
                let offset = args[1].immediate_value();
                builder.bounded_get_element_pointer(
                    builder.backend_ty_from_info(ty),
                    ptr,
                    &[offset],
                )
            }
            Intrinsic::Memcmp | Intrinsic::Memcpy => {
                return;
            }
        };

        if !ret_abi.is_ignored() {
            OperandRef::from_immediate_value_or_scalar_pair(builder, value, result.info)
                .value
                .store(builder, result);
        }
    }

    /// Generate code for a `transmute` intrinsic call. The `transmute`
    /// intrinsic allows for any type to be transmuted into any other type.
    /// This is powerful mechanism that allows for interfacing with code
    /// that requires converting from a potentially opaque type into a known
    /// type.
    pub(super) fn codegen_transmute(
        &mut self,
        builder: &mut Builder,
        src: OperandRef<Builder::Value>,
        dest: PlaceRef<Builder::Value>,
    ) {
        if let Some(value) = self.codegen_transmute_operand(builder, src, dest.info) {
            value.store(builder, dest);
            return;
        }

        match src.value {
            OperandValue::Ref(_, _) | OperandValue::Zero => {
                panic!("value was not handled by `codegen_transmute_operand")
            }
            OperandValue::Immediate(_) | OperandValue::Pair(_, _) => {
                // Allocate a new slot for the `dest.value`, and then
                // store the `src.value` into it.
                src.value
                    .store(builder, PlaceRef::new_aligned(dest.value, src.info, dest.alignment))
            }
        }
    }

    /// Emit code for transmuting from a given operand `src`, generating an
    /// operand value as the destination which will be the result of the
    /// transmute.
    pub(super) fn codegen_transmute_operand(
        &mut self,
        builder: &mut Builder,
        src: OperandRef<Builder::Value>,
        dest: TyInfo,
    ) -> Option<OperandValue<Builder::Value>> {
        if src.info.size() != dest.size() || src.info.is_uninhabited() || dest.is_uninhabited() {
            // So we're trying to cast to an uninhabited type,
            if !src.info.is_uninhabited() {
                builder.codegen_abort_intrinsic();
            }

            // This transmute is UB, we just emit an Poison value so
            // things relying on it can also be marked as Poison.
            //
            // See:
            //  - https://llvm.org/devmtg/2020-09/slides/Lee-UndefPoison.pdf
            //  - https://llvm.org/docs/LangRef.html#poison-values
            return Some(OperandValue::poison(builder, dest));
        }

        let operand_kind = self.op_value_kind(src.info);
        let cast_kind = self.op_value_kind(dest);

        match src.value {
            OperandValue::Ref(ptr, align) => {
                debug_assert_eq!(operand_kind, OperandValueKind::Ref);
                let fake = PlaceRef::new_aligned(ptr, dest, align);
                Some(builder.load_operand(fake).value)
            }
            OperandValue::Immediate(value) => {
                let OperandValueKind::Immediate(in_scalar) = operand_kind else {
                    panic!("found non-immediate operand value for immediate operand");
                };

                if let OperandValueKind::Immediate(out_scalar) = cast_kind {
                    // Ensure everything is the same size...
                    if in_scalar.size(self.ctx) != out_scalar.size(self.ctx) {
                        return None;
                    }

                    let op_ty = builder.backend_ty_from_info(src.info);
                    let cast_ty = builder.backend_ty_from_info(dest);

                    Some(OperandValue::Immediate(self.codegen_transmute_immediate(
                        builder, value, in_scalar, op_ty, out_scalar, cast_ty,
                    )))
                } else {
                    None
                }
            }
            OperandValue::Pair(value_a, value_b) => {
                let OperandValueKind::Pair(in_a_scalar, in_b_scalar) = operand_kind else {
                    panic!("found non-pair operand value for pair operand");
                };

                if let OperandValueKind::Pair(out_a_scalar, out_b_scalar) = cast_kind {
                    // Ensure everything is the same size...
                    if in_a_scalar.size(self.ctx) != out_a_scalar.size(self.ctx)
                        || in_b_scalar.size(self.ctx) != out_b_scalar.size(self.ctx)
                    {
                        return None;
                    }

                    let in_a_ty = builder.scalar_pair_element_backend_ty(src.info, 0, false);
                    let in_b_ty = builder.scalar_pair_element_backend_ty(src.info, 1, false);
                    let out_a_ty = builder.scalar_pair_element_backend_ty(dest, 0, false);
                    let out_b_ty = builder.scalar_pair_element_backend_ty(dest, 1, false);

                    let value_a = self.codegen_transmute_immediate(
                        builder,
                        value_a,
                        in_a_scalar,
                        in_a_ty,
                        out_a_scalar,
                        out_a_ty,
                    );
                    let value_b = self.codegen_transmute_immediate(
                        builder,
                        value_b,
                        in_b_scalar,
                        in_b_ty,
                        out_b_scalar,
                        out_b_ty,
                    );

                    Some(OperandValue::Pair(value_a, value_b))
                } else {
                    None
                }
            }
            OperandValue::Zero => {
                debug_assert_eq!(operand_kind, OperandValueKind::Zero);
                match cast_kind {
                    OperandValueKind::Zero => Some(OperandValue::Zero),
                    _ => None,
                }
            }
        }
    }

    /// Emit code for transmuting between two [Scalar] values. Depending on what
    /// the [ScalarKind]s of the `src` and `dst` is, we emit slightly different
    /// code.
    fn codegen_transmute_immediate(
        &self,
        builder: &mut Builder,
        mut value: Builder::Value,
        from_scalar: abi::Scalar,
        _from_ty: Builder::Type,
        to_scalar: abi::Scalar,
        to_ty: Builder::Type,
    ) -> Builder::Value {
        debug_assert_eq!(from_scalar.size(self.ctx), to_scalar.size(self.ctx));

        value = builder.value_from_immediate(value);

        // @@ValidRanges: When scalars are passed by value, there's no metadata
        // recording their valid ranges. For example, `char`s are passed as just
        // `i32`, with no way for LLVM to know that they're 0x10FFFF at most.
        // Thus we assume the range of the input value too, not just the output
        // range. self.assume_valid_scalar_range(builder, value, from_scalar,
        // from_ty);

        // We need to generate some additional code based on the `from -> to`
        use abi::ScalarKind::*;

        match (from_scalar.kind(), to_scalar.kind()) {
            (Int { .. } | Float { .. }, Int { .. } | Float { .. }) => {
                builder.bit_cast(value, to_ty)
            }
            (Int { .. }, Pointer(_)) => builder.int_to_ptr(value, to_ty),
            (Pointer(_), Int { .. }) => builder.ptr_to_int(value, to_ty),
            // cast the float to an int, and then do `int_to_ptr`.
            (Float { .. }, Pointer(_)) => {
                let int_imm = builder.bit_cast(value, builder.ctx().type_isize());
                builder.int_to_ptr(int_imm, to_ty)
            }
            // Backwards, convert pointer to int, and then bit cast to a float.
            (Pointer(_), Float { .. }) => {
                let int_imm = builder.ptr_to_int(value, builder.ctx().type_isize());
                builder.bit_cast(int_imm, to_ty)
            }
            (Pointer(_), Pointer(_)) => builder.pointer_cast(value, to_ty),
        };

        // @@ValidRanges: do this!
        // self.assume_valid_scalar_range(builder, value, to_scalar, to_ty);
        value = builder.to_immediate_scalar(value, to_scalar);
        value
    }
}
