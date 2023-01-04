//! Defines the lowering process for Hash IR operands into the
//! target backend.

use hash_target::alignment::Alignment;

use crate::layout::TyInfo;

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
