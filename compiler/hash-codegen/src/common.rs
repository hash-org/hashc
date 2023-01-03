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
/// https://llvm.org/doxygen/classllvm_1_1Type.html#a5e9e1c0dd93557be1b4ad72860f3cbda
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
    /// https://llvm.org/doxygen/classllvm_1_1Metadata.html
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
