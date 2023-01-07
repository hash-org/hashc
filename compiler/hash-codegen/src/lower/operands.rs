//! Defines the lowering process for Hash IR operands into the
//! target backend.

use hash_target::alignment::Alignment;

use super::{place::PlaceRef, utils};
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
    pub fn from_immediate(value: V, info: TyInfo) -> Self {
        Self { value: OperandValue::Immediate(value), info }
    }
}
