//! Defines the lowering process for Hash IR operands into the
//! target backend.

use hash_ir::ir;
use hash_layout::TyInfo;
use hash_target::{abi::AbiRepresentation, alignment::Alignment};
use hash_utils::store::{SequenceStore, Store};

use super::{locals::LocalRef, place::PlaceRef, utils, FnBuilder};
use crate::{
    common::MemFlags,
    traits::{
        builder::BlockBuilderMethods, constants::BuildConstValueMethods, ctx::HasCtxMethods,
        layout::LayoutMethods, ty::BuildTypeMethods, CodeGen, CodeGenObject,
    },
};

/// Represents an operand value for the IR. The `V` is a backend
/// specific value type.
#[derive(Clone, Copy)]
pub enum OperandValue<V> {
    /// A reference to an actual operand value.
    Ref(V, Alignment),

    /// An immediate/constant value.
    Immediate(V),

    /// A pair of values, which is supported by a few instructions (
    /// particularly for checked operations; amongst other things).
    Pair(V, V),
}

impl<'b, V: CodeGenObject> OperandValue<V> {
    /// Store the [OperandValue] into the given [PlaceRef] destination.
    pub fn store<Builder: BlockBuilderMethods<'b, Value = V>>(
        self,
        builder: &mut Builder,
        destination: PlaceRef<V>,
    ) {
        self.store_with_flags(builder, destination, MemFlags::empty());
    }

    fn store_with_flags<Builder: BlockBuilderMethods<'b, Value = V>>(
        self,
        builder: &mut Builder,
        destination: PlaceRef<V>,
        flags: MemFlags,
    ) {
        let layout_info = builder.layout_info(destination.info.layout);

        // We don't emit storing of zero-sized types, because they don't
        // actually take up any space and the only way to mimic this would
        // be to emit a `undef` value for the store, which would then
        // be eliminated by the backend (which would be useless).
        if layout_info.is_zst() {
            return;
        }

        match self {
            OperandValue::Ref(value, source_alignment) => {
                // Since `memcpy` does not support non-temporal stores, we
                // need to load the value from the source, and then store
                // it into the destination.
                if flags.contains(MemFlags::NON_TEMPORAL) {
                    todo!()
                }

                utils::mem_copy_ty(
                    builder,
                    (destination.value, destination.alignment),
                    (value, source_alignment),
                    destination.info,
                    flags,
                )
            }
            OperandValue::Immediate(value) => {
                let value = builder.bool_from_immediate(value);
                builder.store_with_flags(value, destination.value, destination.alignment, flags);
            }
            OperandValue::Pair(value_a, value_b) => {
                let AbiRepresentation::Pair(scalar_a, scalar_b) = layout_info.abi else {
                    panic!("invalid ABI representation for a pair operand value");
                };

                let ty = builder.backend_type(destination.info);

                // Emit the code to place the value into the first slot...
                let ptr = builder.structural_get_element_pointer(ty, destination.value, 0);
                let value = builder.bool_from_immediate(value_a);
                let alignment = destination.alignment;

                builder.store_with_flags(value, ptr, alignment, flags);

                // Then deal with the second field...
                let b_offset = scalar_a.size(builder).align_to(scalar_b.align(builder).abi);

                let ptr = builder.structural_get_element_pointer(ty, destination.value, 1);
                let value = builder.bool_from_immediate(value_b);
                let alignment = destination.alignment.restrict_to(b_offset);
                builder.store_with_flags(value, ptr, alignment, flags);
            }
        }
    }
}

/// Represents an operand within the IR. The `V` is a backend specific
/// value type.
#[derive(Clone, Copy)]
pub struct OperandRef<V> {
    /// The value of the operand.
    pub value: OperandValue<V>,

    /// The alignment and type of the operand.
    pub info: TyInfo,
}

impl<'b, V: CodeGenObject> OperandRef<V> {
    /// Create a new zero-sized type [OperandRef].
    pub fn new_zst<Builder: CodeGen<'b, Value = V>>(builder: &Builder, info: TyInfo) -> Self {
        Self {
            value: OperandValue::Immediate(
                builder.const_undef(builder.immediate_backend_type(info)),
            ),
            info,
        }
    }

    /// Create a new [OperandRef] from an immediate value.
    pub fn from_immediate_value(value: V, info: TyInfo) -> Self {
        Self { value: OperandValue::Immediate(value), info }
    }

    /// Assume that the [OperandRef] is an immediate value, and
    /// convert the [OperandRef] into an immediate value.
    pub fn immediate_value(self) -> V {
        match self.value {
            OperandValue::Immediate(value) => value,
            _ => panic!("not an immediate value"),
        }
    }

    /// Apply a dereference operation on a [OperandRef], effectively
    /// producing a [PlaceRef].
    pub fn deref<Builder: LayoutMethods<'b>>(self, builder: &Builder) -> PlaceRef<V> {
        let projected_ty =
            builder.ir_ctx().tys().map_fast(self.info.ty, |ty| ty.on_deref()).unwrap();

        // If we have a pair, then we move the extra data into the place ref.
        let ptr_value = match self.value {
            OperandValue::Immediate(value) => value,

            // This will not occur since we don't have unsized pointer
            // references (i.e. fat pointers).
            OperandValue::Pair(..) => panic!("cannot perform deref on pair value"),
            OperandValue::Ref(..) => panic!("deref on a by-ref operand"),
        };

        let info = builder.layout_of_id(projected_ty);
        let layout = builder.layout_info(info.layout);

        PlaceRef { value: ptr_value, info, alignment: layout.alignment.abi }
    }

    /// Compute a new [OperandRef] from the current operand and a field
    /// projection.
    pub fn extract_field<Builder: BlockBuilderMethods<'b, Value = V>>(
        &self,
        builder: &mut Builder,
        index: usize,
    ) -> Self {
        let layout_info = builder.layout_info(self.info.layout);

        let field_info = self.info.field(builder.layout_ctx(), index);
        let field_layout = builder.layout_info(field_info.layout);

        // If the field is a ZST, we return early
        if field_layout.is_zst() {
            return Self::new_zst(builder, field_info);
        }

        let field_offset = field_layout.shape.offset(index);

        let mut value = match (self.value, field_layout.abi) {
            // The new type is a scalar, pair, or vector.
            (OperandValue::Pair(..) | OperandValue::Immediate(_), _)
                if field_layout.size == layout_info.size =>
            {
                assert_eq!(field_offset.bytes(), 0);
                self.value
            }
            (OperandValue::Pair(value_a, value_b), AbiRepresentation::Pair(scalar_a, scalar_b)) => {
                if field_offset.bytes() == 0 {
                    debug_assert_eq!(field_layout.size, scalar_a.size(builder.ctx()));
                    OperandValue::Immediate(value_a)
                } else {
                    debug_assert_eq!(
                        field_offset,
                        scalar_a.size(builder.ctx()).align_to(scalar_b.align(builder.ctx()).abi)
                    );
                    debug_assert_eq!(field_layout.size, scalar_b.size(builder.ctx()));
                    OperandValue::Immediate(value_b)
                }
            }
            _ => unreachable!("cannot extract field from this operand"),
        };

        // Convert booleans into `i1`s for immediate and pairs, everything
        // else should be unreachable.
        //
        // @@BitCasts: since LLVM requires pointer types (we apply a bitcast here),
        // The bitcasts can be removed, unless we don't use LLVM 15.
        match (&mut value, field_layout.abi) {
            (OperandValue::Immediate(value), _) => {
                *value = builder.to_immediate(*value, field_info.layout);

                // @@BitCasts
                *value = builder.bit_cast(*value, builder.immediate_backend_type(field_info));
            }
            (OperandValue::Pair(value_a, value_b), AbiRepresentation::Pair(scalar_a, scalar_b)) => {
                *value_a = builder.to_immediate_scalar(*value_a, scalar_a);
                *value_b = builder.to_immediate_scalar(*value_b, scalar_b);

                // @@BitCasts
                *value_a = builder.bit_cast(
                    *value_a,
                    builder.scalar_pair_element_backend_type(field_info, 0, true),
                );
                *value_b = builder.bit_cast(
                    *value_b,
                    builder.scalar_pair_element_backend_type(field_info, 0, true),
                );
            }
            (OperandValue::Pair(..), _) => unreachable!(),
            (OperandValue::Ref(..), _) => unreachable!(),
        }

        OperandRef { value, info: field_info }
    }
}

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {
    /// Generate code for a [Operand].
    pub(super) fn codegen_operand(
        &mut self,
        builder: &mut Builder,
        operand: &ir::Operand,
    ) -> OperandRef<Builder::Value> {
        match operand {
            ir::Operand::Place(place) => self.codegen_consume_operand(builder, *place),
            ir::Operand::Const(ref constant) => {
                let ty = constant.ty(builder.ir_ctx());
                let info = builder.layout_of(ty);

                let value = match constant {
                    ir::ConstKind::Value(const_value) => match const_value {
                        ir::Const::Zero(_) => return OperandRef::new_zst(builder, info),
                        value @ (ir::Const::Bool(_)
                        | ir::Const::Char(_)
                        | ir::Const::Int(_)
                        | ir::Const::Float(_)) => {
                            let ty = builder.immediate_backend_type(info);
                            let AbiRepresentation::Scalar(scalar) = builder.layout_info(info.layout).abi else {
                                panic!("scalar constant doesn't have a scalar ABI rerpresentation")
                            };

                            // We convert the constant to a backend equivalent scalar
                            // value and then emit it as an immediate operand value.
                            let value = builder.const_scalar_value(*value, scalar, ty);
                            OperandValue::Immediate(value)
                        }
                        ir::Const::Str(interned_str) => {
                            let (ptr, size) = builder.const_interned_str(*interned_str);
                            OperandValue::Pair(ptr, size)
                        }
                    },
                    ir::ConstKind::Unevaluated(_) => {
                        panic!("un-evaluated constant at code generation")
                    }
                };

                OperandRef { value, info }
            }
        }
    }

    /// Generate code for consuming an "operand", i.e. generate code that
    /// resolves the references [Place] and the load it from memory as
    /// a [OperandRef].
    pub(super) fn codegen_consume_operand(
        &mut self,
        builder: &mut Builder,
        place: ir::Place,
    ) -> OperandRef<Builder::Value> {
        // compute the type of the place and the corresponding layout...
        let info = self.compute_place_ty_info(builder, place);
        let layout = builder.layout_info(info.layout);

        if layout.is_zst() {
            return OperandRef::new_zst(builder, info);
        }

        // Try generate a direct reference to the operand...
        if let Some(value) = self.maybe_codegen_direct_operand_ref(builder, place) {
            return value;
        }

        // Otherwise, we need to load the operand from memory...
        let place_ref = self.codegen_place(builder, place);
        builder.load_operand(place_ref)
    }

    /// Attempt to generate code for a "direct" operand when it can
    /// be referenced in place rather than looking through an allocation.
    ///
    /// If the operand cannot be represented directly, this function will
    /// return [None].
    pub fn maybe_codegen_direct_operand_ref(
        &mut self,
        builder: &mut Builder,
        place: ir::Place,
    ) -> Option<OperandRef<Builder::Value>> {
        match self.locals[place.local] {
            LocalRef::Operand(Some(mut operand)) => {
                self.ctx.ir_ctx().projections().map_fast(place.projections, |projections| {
                    for projection in projections {
                        match *projection {
                            ir::PlaceProjection::Field(index) => {
                                operand = operand.extract_field(builder, index);
                            }
                            ir::PlaceProjection::Index(_)
                            | ir::PlaceProjection::ConstantIndex { .. } => {
                                let element_info = operand.info.field(builder.layout_ctx(), 0);
                                let element_layout = builder.layout_info(element_info.layout);

                                if element_layout.is_zst() {
                                    operand = OperandRef::new_zst(builder, element_info)
                                } else {
                                    return None;
                                }
                            }
                            _ => return None,
                        }
                    }

                    Some(operand)
                })
            }
            LocalRef::Operand(None) => {
                panic!("use of operand before defiition")
            }

            // We don't deal with locals that refer to a place, and
            // thus they can't be directly referenced.
            LocalRef::Place(_) => None,
        }
    }
}
