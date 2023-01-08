//! Common data structures and parameters that are used by the code generation
//! backend and trait definitions.

use bitflags::bitflags;

/// Checked operations that a compiler backend can perform. All of these
/// operations are checking the correctness of arithmetic operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CheckedOp {
    /// Addition
    Add,

    /// Subtraction
    Sub,

    /// Multiplication
    Mul,

    /// Division
    Div,

    /// Remainder
    Rem,
}

/// This defines all of the type "kinds" that are used by LLVM.
///
/// <https://llvm.org/doxygen/classllvm_1_1Type.html#a5e9e1c0dd93557be1b4ad72860f3cbda>
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeKind {
    /// 16-bit floating point type.
    HalfTy,

    /// 16-bit floating point type (7-bit mantissa).
    BFloatTy,

    /// 32-bit floating point type.
    FloatTy,

    /// 64-bit floating point type.
    DoubleTy,

    /// 80-bit floating point type (X87).
    X86FP80Ty,

    /// 128-bit floating point type (112-bit mantissa).
    FP128Ty,

    /// 128-bit floating point type (two 64-bits, PowerPC).
    PPCFP128Ty,

    /// Void type, no size.
    VoidTy,

    /// Label type, only used as function return type.
    LabelTy,

    /// Metadata type, only used in LLVM metadata.
    ///
    /// More information can be found here:
    /// <https://llvm.org/doxygen/classllvm_1_1Metadata.html>
    MetadataTy,

    /// X86 MMX vector type (64 bits, X86 specific).
    X86MMXTy,

    /// X86 AMX vector type (8192 bits, X86 specific).
    X86AMXTy,

    /// Token type, only used in LLVM metadata.
    TokenTy,

    /// Integer types
    IntegerTy,

    /// Function types
    FunctionTy,

    /// Pointer types
    PointerTy,

    /// Structure types
    StructTy,

    /// Array types
    ArrayTy,

    /// Fixed vector types
    FixedVectorTy,

    /// Scalable vector types
    ScalableVectorTy,

    /// Typed pointer types
    TypedPointerTy,

    /// Target extension types
    TargetExtensionTy,
}

/// Rerpesents all of the comparison kinds that can occur between
/// two integer operands. This is a backend-agnostic representation
/// of the comparison kinds.
///
/// This is a direct mapping of LLVM `IntPredicate` types:
/// <https://llvm.org/doxygen/classllvm_1_1CmpInst.html#a2be3583dac92a031fa1458d4d992c78b>
#[derive(Clone, Copy)]
pub enum IntComparisonKind {
    /// Equal integer comparison.
    Eq,

    /// Not-equal integer comparison.
    Ne,

    /// Unsigned greater-than integer comparison.
    Ugt,

    /// Unsigned greater-than-or-equal integer comparison.
    Uge,

    /// Unsigned less-than integer comparison.
    Ult,

    /// Unsigned less-than-or-equal integer comparison.
    Ule,

    /// Signed greater-than integer comparison.
    Sgt,

    /// Signed greater-than-or-equal integer comparison.
    Sge,

    /// Signed less-than integer comparison.
    Slt,

    /// Signed less-than-or-equal integer comparison.
    Sle,
}

/// Represents all of the comparison kinds that can occur between
/// two floating point operands. This is a backend-agnostic representation
/// of the comparison kinds.
///
/// This is a direct mapping of LLVM `RealPredicate` types:
/// <https://llvm.org/doxygen/classllvm_1_1CmpInst.html#a2be3583dac92a031fa1458d4d992c78b>
pub enum RealComparisonKind {
    /// Folded comparison, always equal to "false".
    False,

    /// Ordered and equal.
    Oeq,

    /// Ordered and greater than.
    Ogt,

    /// Ordered and greater than or equal.
    Oge,

    /// Ordered and less than.
    Olt,

    /// Ordered and less than or equal.
    Ole,

    /// Ordered and not equal.
    One,

    /// Ordered (no nans).
    Ord,

    /// Unordered: isnan(X) | isnan(Y).
    Uno,

    /// Unordered or equal.
    Ueq,

    /// Unordered or greater than.
    Ugt,

    /// Unordered or greater than or equal.
    Uge,

    /// Unordered or less than.
    Ult,

    /// Unordered or less than or equal.
    Ule,

    /// Unordered or not equal.
    Une,

    /// Folded comparison, always equal to "true".
    True,
}

bitflags! {
    /// Defines a collection of memory flags that can specify a cell of
    /// memory that LLVM and other backends that may support it.
    pub struct MemFlags: u8 {
        /// The memory slot is marked as a volatile region.
        const VOLATILE = 1 << 0;

        /// This flag specifies to the LLVM Optimiser that the memory is
        /// not expected to be re-used and thus should not be cached. This
        /// is useful for things like atomic operations
        ///
        /// Ref: https://llvm.org/docs/LangRef.html#store-instruction
        const NON_TEMPORAL = 1 << 1;
    }
}
