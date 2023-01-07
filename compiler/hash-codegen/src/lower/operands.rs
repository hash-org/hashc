//! Defines the lowering process for Hash IR operands into the
//! target backend.

use hash_target::alignment::Alignment;

use crate::{
    layout::TyInfo,
    traits::{constants::BuildConstValueMethods, ty::BuildTypeMethods, CodeGen, CodeGenObject},
};

/// Represents an operand value for the IR. The `V` is a backend
/// specific value type.
pub enum OperandValue<V> {
    /// A reference to an actual operand value.
    Ref(V, Alignment),

    /// An immediate/constant value.
    Immediate(V),

    /// A pair of values, which is supported by a few instructions (
    /// particularly for checked operations; amongst other things).
    Pair(V, V),
}

/// Represents an operand within the IR. The `V` is a backend specific
/// value type.
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
