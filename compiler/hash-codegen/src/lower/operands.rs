//! Defines the lowering process for Hash IR operands into the
//! target backend.

use hash_ir::ir::{Operand, Place};
use hash_target::alignment::Alignment;

use super::{place::PlaceRef, utils, FnBuilder};
use crate::{
    common::MemFlags,
    layout::TyInfo,
    traits::{
        builder::BlockBuilderMethods, constants::BuildConstValueMethods, ctx::HasCtxMethods,
        ty::BuildTypeMethods, CodeGen, CodeGenObject,
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
        // We don't emit storing of zero-sized types, because they don't
        // actually take up any space and the only way to mimic this would
        // be to emit a `undef` value for the store, which would then
        // be eliminated by the backend (which would be useless).
        if builder.layout_info(destination.info.layout).is_zst() {
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
            OperandValue::Pair(_, _) => {
                todo!()
            }
        }
    }
}

impl<'b, Builder: BlockBuilderMethods<'b>> FnBuilder<'b, Builder> {
    /// Generate code for a [Operand].
    pub(super) fn codegen_operand(
        &mut self,
        builder: &mut Builder,
        operand: &Operand,
    ) -> OperandRef<Builder::Value> {
        match operand {
            Operand::Place(place) => self.codegen_consume_operand(builder, *place),
            Operand::Const(ref _constant) => {
                todo!()
            }
        }
    }

    /// Generate code for consuming an "operand", i.e. generate code that
    /// resolves the references [Place] and the load it from memory as
    /// a [OperandRef].
    pub(super) fn codegen_consume_operand(
        &mut self,
        builder: &mut Builder,
        place: Place,
    ) -> OperandRef<Builder::Value> {
        // compute the type of the place and the corresponding layout...
        let info = self.compute_place_ty_info(builder, place);
        let layout = builder.layout_info(info.layout);

        if layout.is_zst() {
            return OperandRef::new_zst(builder, info);
        }

        // Try generate a direct reference to the operand...
        if let Some(value) = self.codegen_direct_operand_ref(builder, place) {
            return value;
        }

        // Otherwise, we need to load the operand from memory...
        let place_ref = self.codegen_place(builder, place);
        builder.load_operand(place_ref)
    }

    pub fn codegen_direct_operand_ref(
        &mut self,
        _builder: &mut Builder,
        _place: Place,
    ) -> Option<OperandRef<Builder::Value>> {
        todo!()
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
}
