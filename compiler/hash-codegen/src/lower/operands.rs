//! Defines the lowering process for Hash IR operands into the
//! target backend.

use hash_ir::{
    constant::{AllocId, AllocRange, Const, ConstKind},
    ir,
};
use hash_layout::TyInfo;
use hash_storage::store::statics::StoreId;
use hash_target::{
    abi::{self, AbiRepresentation},
    alignment::Alignment,
    size::Size,
};

use super::{locals::LocalRef, place::PlaceRef, utils, FnBuilder};
use crate::{
    common::MemFlags,
    traits::{
        builder::BlockBuilderMethods, constants::ConstValueBuilderMethods, layout::LayoutMethods,
        statics::StaticMethods, ty::TypeBuilderMethods, CodeGenObject,
    },
};

/// Represents the kind of [OperandValue] that is expected for a
/// type. This includes useful information about the ABI representation
/// of the type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperandValueKind {
    // Zero sized.
    Zero,

    /// An immediate value, with the given scalar kind.
    Immediate(abi::Scalar),

    /// A pair of immediate values, with the given scalar kinds.
    Pair(abi::Scalar, abi::Scalar),

    /// A reference to an actual operand value.
    Ref,
}

/// Represents an operand value for the IR. The `V` is a backend
/// specific value type.
#[derive(Clone, Copy, Debug)]
pub enum OperandValue<V: std::fmt::Debug> {
    /// A reference to an actual operand value.
    Ref(V, Alignment),

    /// An immediate/constant value.
    Immediate(V),

    /// A pair of values, which is supported by a few instructions (
    /// particularly for checked operations; amongst other things).
    Pair(V, V),

    /// A zero sized value.
    Zero,
}

impl<'a, 'b, V: CodeGenObject> OperandValue<V> {
    /// Generate an [OperandValue] that is considered to be **poisoned**. In
    /// principle, this means that any operations that is being applied on
    /// the value itself is then also **poisoned**.
    ///
    /// This function will return a poisoned value for the given [OperandValue].
    pub fn poison<Builder: BlockBuilderMethods<'a, 'b, Value = V>>(
        builder: &Builder,
        info: TyInfo,
    ) -> OperandValue<Builder::Value> {
        if info.is_zst() {
            OperandValue::Zero
        } else if builder.is_backend_immediate(info) {
            let ty = builder.immediate_backend_ty(info);
            OperandValue::Immediate(builder.const_undef(ty))
        } else if builder.is_backend_scalar_pair(info) {
            let a_ty = builder.scalar_pair_element_backend_ty(info, 0, true);
            let b_ty = builder.scalar_pair_element_backend_ty(info, 1, true);
            OperandValue::Pair(builder.const_undef(a_ty), builder.const_undef(b_ty))
        } else {
            let ptr = builder.ctx().type_ptr();
            OperandValue::Ref(builder.const_undef(ptr), info.abi_alignment())
        }
    }

    /// Store the [OperandValue] into the given [PlaceRef] destination.
    pub fn store<Builder: BlockBuilderMethods<'a, 'b, Value = V>>(
        self,
        builder: &mut Builder,
        destination: PlaceRef<V>,
    ) {
        self.store_with_flags(builder, destination, MemFlags::empty());
    }

    fn store_with_flags<Builder: BlockBuilderMethods<'a, 'b, Value = V>>(
        self,
        builder: &mut Builder,
        destination: PlaceRef<V>,
        flags: MemFlags,
    ) {
        let abi = destination.info.layout.map(|layout| layout.abi);

        match self {
            OperandValue::Zero => {
                // We don't emit storing of zero-sized types, because they don't
                // actually take up any space and the only way to mimic this
                // would be to emit a `undef` value for the
                // store, which would then be eliminated by the
                // backend (which would be useless).
            }
            OperandValue::Ref(value, source_alignment) => {
                // Since `memcpy` does not support non-temporal stores, we
                // need to load the value from the source, and then store
                // it into the destination.
                if flags.contains(MemFlags::NON_TEMPORAL) {
                    let ty = builder.backend_ty_from_info(destination.info);
                    let value = builder.load(ty, value, source_alignment);

                    builder.store_with_flags(
                        value,
                        destination.value,
                        destination.alignment,
                        flags,
                    );
                    return;
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
                let value = builder.value_from_immediate(value);
                builder.store_with_flags(value, destination.value, destination.alignment, flags);
            }
            OperandValue::Pair(value_a, value_b) => {
                let AbiRepresentation::Pair(scalar_a, scalar_b) = abi else {
                    panic!("invalid ABI representation for a pair operand value: `{abi:?}`");
                };

                let ty = builder.backend_ty_from_info(destination.info);

                // Emit the code to place the value into the first slot...
                let ptr = builder.structural_get_element_pointer(ty, destination.value, 0);
                let value = builder.value_from_immediate(value_a);
                let alignment = destination.alignment;

                builder.store_with_flags(value, ptr, alignment, flags);

                // Then deal with the second field...
                let b_offset = scalar_a.size(builder).align_to(scalar_b.align(builder).abi);

                let ptr = builder.structural_get_element_pointer(ty, destination.value, 1);
                let value = builder.value_from_immediate(value_b);
                let alignment = destination.alignment.restrict_to(b_offset);
                builder.store_with_flags(value, ptr, alignment, flags);
            }
        }
    }
}

/// Represents an operand within the IR. The `V` is a backend specific
/// value type.
#[derive(Clone, Copy, Debug)]
pub struct OperandRef<V: std::fmt::Debug> {
    /// The value of the operand.
    pub value: OperandValue<V>,

    /// The alignment and type of the operand.
    pub info: TyInfo,
}

impl<'a, 'b, V: CodeGenObject> OperandRef<V> {
    /// Create a new zero-sized type [OperandRef].
    pub fn zst(info: TyInfo) -> Self {
        Self { value: OperandValue::Zero, info }
    }

    /// Create a new [OperandRef] from an immediate value or a packed
    /// scalar pair value.
    pub fn from_immediate_value_or_scalar_pair<Builder: BlockBuilderMethods<'a, 'b, Value = V>>(
        builder: &mut Builder,
        value: V,
        info: TyInfo,
    ) -> Self {
        let abi = info.layout.borrow().abi;

        let value = if let AbiRepresentation::Pair(scalar_a, scalar_b) = abi {
            // Construct the aggregate value...
            let value_a = builder.extract_field_value(value, 0);
            let value_a = builder.to_immediate_scalar(value_a, scalar_a);

            let value_b = builder.extract_field_value(value, 1);
            let value_b = builder.to_immediate_scalar(value_b, scalar_b);

            OperandValue::Pair(value_a, value_b)
        } else {
            OperandValue::Immediate(value)
        };
        Self { value, info }
    }

    /// Assume that the [OperandRef] is an immediate value, and
    /// convert the [OperandRef] into an immediate value.
    pub fn immediate_value(self) -> V {
        match self.value {
            OperandValue::Immediate(value) => value,
            _ => panic!("not an immediate value"),
        }
    }

    /// Assume that the [OperandRef] is a [`OperandValue::Pair`], and we
    /// construct a pair value from this.
    pub fn immediate_or_scalar_pair<Builder: BlockBuilderMethods<'a, 'b, Value = V>>(
        self,
        builder: &mut Builder,
    ) -> V {
        if let OperandValue::Pair(a, b) = self.value {
            let ty = builder.backend_ty_from_info(self.info);

            let mut pair = builder.const_undef(ty);
            let immediate_a = builder.value_from_immediate(a);
            let immediate_b = builder.value_from_immediate(b);
            pair = builder.insert_field_value(pair, immediate_a, 0);
            pair = builder.insert_field_value(pair, immediate_b, 1);
            pair
        } else {
            self.immediate_value()
        }
    }

    /// Constructr an [OperandRef] from an [ir::Const] value.
    pub fn from_const<Builder: BlockBuilderMethods<'a, 'b, Value = V>>(
        builder: &mut Builder,
        constant: &Const,
    ) -> Self {
        let info = builder.layout_of(constant.ty());

        let value = match constant.kind() {
            ConstKind::Zero => return OperandRef::zst(info),
            ConstKind::Scalar(value) => {
                // Ensure that the computer ABI is a scalar.
                let AbiRepresentation::Scalar(scalar) = info.layout.borrow().abi else {
                    panic!(
                        "`from_const` ABI representation of scalar is not a scalar, but `{:?}`",
                        info.layout.borrow().abi
                    )
                };

                // We convert the constant to a backend equivalent scalar
                // value and then emit it as an immediate operand value.
                let ty = builder.immediate_backend_ty(info);
                let value = builder.const_scalar_value(value, scalar, ty);
                OperandValue::Immediate(value)
            }
            ConstKind::Pair { data, .. } => {
                // Ensure that the computer ABI is a scalar-pair.
                let AbiRepresentation::Pair(_, _) = info.layout.borrow().abi else {
                    panic!(
                        "`from_const` ABI representation of pair is not a pair, but `{:?}`",
                        info.layout.borrow().abi
                    )
                };

                let (ptr, size) = builder.const_str(data);
                OperandValue::Pair(ptr, size)
            }
            ConstKind::Alloc { offset, alloc } => {
                return Self::from_alloc(builder, info, alloc, offset)
            }
        };

        OperandRef { value, info }
    }

    pub fn from_alloc<Builder: BlockBuilderMethods<'a, 'b, Value = V>>(
        builder: &mut Builder,
        info: TyInfo,
        alloc: AllocId,
        offset: Size,
    ) -> Self {
        let alloc_align = alloc.borrow().align();
        // Ensure that the alignment of the allocation is the same as the
        // computed alignment of the type.
        debug_assert_eq!(alloc_align, info.abi_alignment());

        // Read a leaf (or in other words a `Scalar`) from the allocation.
        let read_scalar = |start, size, abi: abi::Scalar, ty| {
            let value = alloc.borrow().read_scalar(AllocRange::new(start, size), builder);
            builder.const_scalar_value(value, abi, ty)
        };

        match info.layout.borrow().abi {
            AbiRepresentation::Scalar(a @ abi::Scalar::Initialised { .. }) => {
                let size = a.size(builder);
                assert_eq!(size, info.size(), "abi::Scalar size does not match layout size");
                let val = read_scalar(Size::ZERO, size, a, builder.type_ptr());
                OperandRef { value: OperandValue::Immediate(val), info }
            }
            AbiRepresentation::Pair(
                a @ abi::Scalar::Initialised { .. },
                b @ abi::Scalar::Initialised { .. },
            ) => {
                let (a_size, b_size) = (a.size(builder), b.size(builder));
                let b_offset = a_size.align_to(b.align(builder).abi);
                assert!(b_offset.bytes() > 0);

                let a_val = read_scalar(
                    Size::ZERO,
                    a_size,
                    a,
                    builder.scalar_pair_element_backend_ty(info, 0, true),
                );

                let b_val = read_scalar(
                    b_offset,
                    b_size,
                    b,
                    builder.scalar_pair_element_backend_ty(info, 1, true),
                );

                OperandRef { value: OperandValue::Pair(a_val, b_val), info }
            }
            _ if info.is_zst() => OperandRef::zst(info),
            // Not a scalar, or pair, or zero-sized type.
            _ => {
                let init = builder.const_data_from_alloc(alloc);

                // We need to compute the base address of the constant.
                let base_addr = builder.static_addr_of(init, alloc_align);

                let value = builder.const_ptr_byte_offset(base_addr, offset);
                builder.load_operand(PlaceRef::new(value, info))
            }
        }
    }

    /// Apply a dereference operation on a [OperandRef], effectively
    /// producing a [PlaceRef].
    pub fn deref<Builder: LayoutMethods<'b>>(self, builder: &Builder) -> PlaceRef<V> {
        let projected_ty = self.info.ty.borrow().on_deref().unwrap();

        // If we have a pair, then we move the extra data into the place ref.
        let (ptr_value, extra) = match self.value {
            OperandValue::Immediate(value) => (value, None),
            OperandValue::Pair(value, extra) => (value, Some(extra)),
            OperandValue::Ref(..) => panic!("deref on a by-ref operand"),
            OperandValue::Zero => panic!("deref on a zero-sized type"),
        };

        let info = builder.layout_of(projected_ty);
        let alignment = info.abi_alignment();

        PlaceRef { value: ptr_value, extra, info, alignment }
    }

    /// Compute a new [OperandRef] from the current operand and a field
    /// projection.
    pub fn extract_field<Builder: BlockBuilderMethods<'a, 'b, Value = V>>(
        &self,
        builder: &mut Builder,
        index: usize,
    ) -> Self {
        let size = self.info.size();
        let field_info = self.info.field(builder.layouts(), index);
        let (field_abi, field_size, offset) = field_info.layout.map(|field_layout| {
            (field_layout.abi, field_layout.size, field_layout.shape.offset(index))
        });

        let mut value = match (self.value, field_abi) {
            _ if field_info.is_zst() => OperandValue::Zero,
            // The new type is a scalar, pair, or vector.
            (OperandValue::Pair(..) | OperandValue::Immediate(_), _) if field_size == size => {
                assert_eq!(offset.bytes(), 0);
                self.value
            }
            (OperandValue::Pair(value_a, value_b), AbiRepresentation::Pair(scalar_a, scalar_b)) => {
                if offset.bytes() == 0 {
                    debug_assert_eq!(field_size, scalar_a.size(builder.ctx()));
                    OperandValue::Immediate(value_a)
                } else {
                    debug_assert_eq!(
                        offset,
                        scalar_a.size(builder.ctx()).align_to(scalar_b.align(builder.ctx()).abi)
                    );
                    debug_assert_eq!(field_size, scalar_b.size(builder.ctx()));
                    OperandValue::Immediate(value_b)
                }
            }
            _ => unreachable!("cannot extract field from this operand"),
        };

        // Convert booleans into `i1`s for immediate and pairs, everything
        // else should be unreachable.
        match (&mut value, field_abi) {
            (OperandValue::Zero, _) => {}
            (OperandValue::Immediate(value), _) => {
                *value = builder.to_immediate(*value, field_info.layout);
            }
            (OperandValue::Pair(value_a, value_b), AbiRepresentation::Pair(scalar_a, scalar_b)) => {
                *value_a = builder.to_immediate_scalar(*value_a, scalar_a);
                *value_b = builder.to_immediate_scalar(*value_b, scalar_b);
            }
            (OperandValue::Pair(..), _) => unreachable!(),
            (OperandValue::Ref(..), _) => unreachable!(),
        }

        OperandRef { value, info: field_info }
    }
}

impl<'a, 'b, Builder: BlockBuilderMethods<'a, 'b>> FnBuilder<'a, 'b, Builder> {
    /// Generate code for a [Operand].
    pub(super) fn codegen_operand(
        &mut self,
        builder: &mut Builder,
        operand: &ir::Operand,
    ) -> OperandRef<Builder::Value> {
        match operand {
            ir::Operand::Place(place) => self.codegen_consume_operand(builder, *place),
            ir::Operand::Const(constant) => OperandRef::from_const(builder, constant),
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

        if info.is_zst() {
            return OperandRef::zst(info);
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
                for projection in place.projections.borrow().iter() {
                    match *projection {
                        ir::PlaceProjection::Field(index) => {
                            operand = operand.extract_field(builder, index);
                        }
                        ir::PlaceProjection::Index(_)
                        | ir::PlaceProjection::ConstantIndex { .. } => {
                            let element_info = operand.info.field(builder.layouts(), 0);

                            if element_info.is_zst() {
                                operand = OperandRef::zst(element_info)
                            } else {
                                return None;
                            }
                        }
                        _ => return None,
                    }
                }

                Some(operand)
            }
            LocalRef::Operand(None) => {
                panic!("use of operand before definition")
            }

            // We don't deal with locals that refer to a place, and
            // thus they can't be directly referenced.
            LocalRef::Place(_) => None,
        }
    }

    /// Compute the [OperandValueKind] from a given layout.
    pub fn op_value_kind(&self, info: TyInfo) -> OperandValueKind {
        if info.is_zst() {
            OperandValueKind::Zero
        } else if self.ctx.is_backend_immediate(info) {
            OperandValueKind::Immediate(match info.layout.borrow().abi {
                AbiRepresentation::Scalar(scalar) => scalar,
                AbiRepresentation::Vector { kind, .. } => kind,
                _ => panic!("invalid ABI representation for an immediate value"),
            })
        } else if self.ctx.is_backend_scalar_pair(info) {
            let (a, b) = match info.layout.borrow().abi {
                AbiRepresentation::Pair(a, b) => (a, b),
                _ => panic!("invalid ABI representation for a scalar pair"),
            };

            OperandValueKind::Pair(a, b)
        } else {
            OperandValueKind::Ref
        }
    }
}
