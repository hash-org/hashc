//! Module that hosts all of the logic that deals with emitting
//! code and resolving references to intrinsic function calls.

use hash_abi::FnAbi;
use hash_ir::{intrinsics::Intrinsic, ir, ty::IrTy};
use hash_target::abi::{AbiRepresentation, ScalarKind};
use hash_utils::store::Store;

use super::{abi::compute_fn_abi_from_instance, locals::LocalRef, place::PlaceRef, FnBuilder};
use crate::{
    lower::operands::OperandValue,
    traits::{
        builder::BlockBuilderMethods, ctx::HasCtxMethods, misc::MiscBuilderMethods,
        ty::TypeBuilderMethods,
    },
};

impl<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> FnBuilder<'a, 'b, Builder> {
    /// Resolve a reference to an [Intrinsic].
    pub(super) fn resolve_intrinsic(
        &mut self,
        builder: &mut Builder,
        intrinsic: Intrinsic,
    ) -> (FnAbi, Builder::Function) {
        // @@ErrorHandling: propagate the error into the compiler pipeline, thus
        // terminating the workflow if this error occurs which it shouldn't
        let ty = self.ctx.ir_ctx().intrinsics().get(intrinsic).unwrap();

        // Get function pointer from the specified instance
        let instance = self.ctx.ir_ctx().map_ty(ty, |ty| match ty {
            IrTy::FnDef { instance, .. } => *instance,
            _ => panic!("expected function type when resolving intrinsic item"),
        });

        let abi = compute_fn_abi_from_instance(builder, instance).unwrap();
        (abi, builder.get_fn_ptr(instance))
    }

    /// Generate code for a `transmute` intrinsic call. The `transmute`
    /// intrinsic allows for any type to be transmuted into any other type.
    /// This is powerful mechanism that allows for interfacing with code
    /// that requires converting from a potentially opaque type into a known
    /// type.
    pub(super) fn codegen_transmute(
        &mut self,
        builder: &mut Builder,
        src: &ir::Operand,
        dest: ir::Place,
    ) {
        if let Some(local) = dest.as_local() {
            match self.locals[local] {
                LocalRef::Place(place) => self.codegen_transmute_into(builder, src, place),
                LocalRef::Operand(None) => {
                    // We might have to perform some adjustments to the layout of the
                    // destination and source if they mismatch.
                    let dest_layout = self.compute_place_ty_info(builder, dest);

                    let place = PlaceRef::new_stack(builder, dest_layout);
                    place.storage_live(builder);

                    self.codegen_transmute_into(builder, src, place);
                    let op = builder.load_operand(place);
                    place.storage_dead(builder);

                    self.locals[local] = LocalRef::Operand(Some(op));
                }
                LocalRef::Operand(_) => panic!("assigning to operand twice"),
            }
        } else {
            // Generate the place, and then store the value into it.
            let place = self.codegen_place(builder, dest);
            self.codegen_transmute_into(builder, src, place)
        }
    }

    /// Helper function that generates code for a `transmute` to store the value
    /// of `src` into the specified [PlaceRef].
    fn codegen_transmute_into(
        &mut self,
        builder: &mut Builder,
        src: &ir::Operand,
        dest: PlaceRef<Builder::Value>,
    ) {
        let src = self.codegen_operand(builder, src);

        self.ctx.layouts().map_many_fast([src.info.layout, dest.info.layout], |layouts| {
            let (src_layout, dest_layout) = (layouts[0], layouts[1]);

            // Special case for transmuting between pointers and integers.
            if let (AbiRepresentation::Scalar(src_scalar), AbiRepresentation::Scalar(dest_scalar)) =
                (src_layout.abi, dest_layout.abi)
            {
                let is_src_ptr = matches!(src_scalar.kind(), ScalarKind::Pointer(_));
                let is_dest_ptr = matches!(dest_scalar.kind(), ScalarKind::Pointer(_));

                if is_src_ptr == is_dest_ptr {
                    debug_assert_eq!(src_layout.size, dest_layout.size);

                    let src = builder.value_from_immediate(src.immediate_value());

                    // If the source and destination are pointers, we need to cast
                    // the pointer to the destination type.
                    let src_as_dst = if is_src_ptr {
                        builder.pointer_cast(src, builder.backend_ty_from_info(dest.info))
                    } else {
                        builder.bit_cast(src, builder.backend_ty_from_info(dest.info))
                    };

                    // Now store the value into the destination
                    let value = OperandValue::Immediate(
                        builder.to_immediate_scalar(src_as_dst, dest_scalar),
                    );
                    value.store(builder, dest);

                    return;
                }
            }

            // Create a pointer cast
            let ty = builder.backend_ty_from_info(src.info);
            let cast_ptr = builder.pointer_cast(dest.value, builder.type_ptr_to(ty));

            // Store the value into the `cast_ptr` value
            let alignment = src_layout.alignment.abi.min(dest.alignment);
            src.value.store(builder, PlaceRef::new_aligned(cast_ptr, src.info, alignment))
        })
    }
}
