//! Common data structures and parameters that are used by the code generation
//! backend and trait definitions.

use hash_ir::ir;
use hash_utils::bitflags::bitflags;

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
}

/// This defines all of the type "kinds" that are used by LLVM.
///
/// https://llvm.org/doxygen/group__LLVMCCoreTypes.html#ga2da643b0ebe215106a07c8e03f3ad8d8>
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeKind {
    /// Void type, no size.
    Void,

    /// 16-bit floating point type.
    Half,

    /// 32-bit floating point type.
    Float,

    /// 64-bit floating point type.
    Double,

    /// 80-bit floating point type (X87).
    X86FP80,

    /// 128-bit floating point type (112-bit mantissa).
    FP128,

    /// 128-bit floating point type (two 64-bits, PowerPC).
    PPCFP128,

    /// Label type, only used as function return type.
    Label,

    /// Integer types
    Integer,

    /// Function types
    Function,

    /// Structure types
    Struct,

    /// Array types
    Array,

    /// Pointer types.
    Pointer,

    /// Fixed vector types.
    Vector,

    /// Metadata type, only used in LLVM metadata.
    ///
    /// More information can be found here:
    /// <https://llvm.org/doxygen/classllvm_1_1Metadata.html>
    Metadata,

    /// Token type, only used in LLVM metadata.
    Token,

    /// Scalable vector types.
    ScalableVector,

    /// 16-bit floating point type (7-bit mantissa).
    BFloatTy,

    /// X86 AMX vector type (8192 bits, X86 specific).
    X86AMX,

    /// Target extension types
    TargetExtensionTy,
}

/// Represents all of the comparison kinds that can occur between
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

impl IntComparisonKind {
    /// Create a [IntComparisonKind] from a [ir::BinOp] and
    /// a boolean flag specifying if the operands are signed.
    pub fn from_bin_op(operator: ir::BinOp, signed: bool) -> Self {
        match operator {
            ir::BinOp::Eq => Self::Eq,
            ir::BinOp::Neq => Self::Ne,
            ir::BinOp::Gt => {
                if signed {
                    Self::Sgt
                } else {
                    Self::Ugt
                }
            }
            ir::BinOp::GtEq => {
                if signed {
                    Self::Sge
                } else {
                    Self::Uge
                }
            }
            ir::BinOp::Lt => {
                if signed {
                    Self::Slt
                } else {
                    Self::Ult
                }
            }
            ir::BinOp::LtEq => {
                if signed {
                    Self::Sle
                } else {
                    Self::Ule
                }
            }
            _ => unreachable!(),
        }
    }
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

impl TryFrom<ir::BinOp> for RealComparisonKind {
    type Error = ();

    fn try_from(operator: ir::BinOp) -> Result<Self, Self::Error> {
        match operator {
            ir::BinOp::Eq => Ok(Self::Oeq),
            ir::BinOp::Neq => Ok(Self::Une),
            ir::BinOp::Gt => Ok(Self::Ogt),
            ir::BinOp::GtEq => Ok(Self::Oge),
            ir::BinOp::Lt => Ok(Self::Olt),
            ir::BinOp::LtEq => Ok(Self::Ole),
            _ => Err(()),
        }
    }
}

bitflags! {
    /// Defines a collection of memory flags that can specify a cell of
    /// memory that LLVM and other backends that may support it.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct MemFlags: u8 {
        /// The memory slot is marked as a volatile region.
        const VOLATILE = 1 << 0;

        /// This flag specifies to the code generation backend that
        /// this data is not to be re-used and thus should not be cached.
        /// This is useful for things like atomic operations.
        ///
        /// Extract from documentation:
        /// ```text
        /// The existence of the `!nontemporal` metadata on the instruction tells the
        /// optimizer and code generator that this load is not expected to be reused
        /// in the cache. The code generator may select special instructions to save
        /// cache bandwidth, such as the `MOVNT` instruction on x86.
        /// ```
        ///
        /// Ref: https://llvm.org/docs/LangRef.html#store-instruction
        const NON_TEMPORAL = 1 << 1;

        /// When the referred place is considered to be unaligned.
        const UN_ALIGNED = 1 << 2;
    }
}

/// Represents the atomic ordering of an atomic operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtomicOrdering {
    /// No ordering constraints.
    NotAtomic,

    /// No ordering constraints.
    Unordered,

    /// Monotonic ordering.
    Monotonic,

    /// Acquire ordering.
    Acquire,

    /// Release ordering.
    Release,

    /// Acquire and release ordering.
    AcquireRelease,

    /// Sequentially consistent ordering.
    SequentiallyConsistent,
}
