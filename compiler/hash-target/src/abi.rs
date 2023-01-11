//! Contains primitives to define ABIs for various targets. These primitives
//! live in `hash-target` in order to be shared between multiple other crates
//! like `hash-abi` and `hash-codegen`.

use std::fmt;

use crate::{alignment::Alignments, layout::HasDataLayout, size::Size};

/// ABI representation of an integer scalar type.
#[derive(Clone, Copy, Debug)]
pub enum Integer {
    I8,
    I16,
    I32,
    I64,
    I128,
}

impl Integer {
    /// Compute the [Size] of the [Integer].
    #[inline]
    pub fn size(self) -> Size {
        use Integer::*;

        match self {
            I8 => Size::from_bytes(1),
            I16 => Size::from_bytes(2),
            I32 => Size::from_bytes(4),
            I64 => Size::from_bytes(8),
            I128 => Size::from_bytes(16),
        }
    }

    /// Get the [Alignments] of the [Integer].
    pub fn align<C: HasDataLayout>(self, ctx: &C) -> Alignments {
        use Integer::*;
        let dl = ctx.data_layout();

        match self {
            I8 => dl.i8_align,
            I16 => dl.i16_align,
            I32 => dl.i32_align,
            I64 => dl.i64_align,
            I128 => dl.i128_align,
        }
    }
}

/// ABI representation of a float scalar type.
#[derive(Clone, Copy, Debug)]
pub enum Float {
    /// A 32-bit float.
    F32,

    /// A 64-bit float.
    F64,
}

impl Float {
    /// Compute the [Size] of the [Float].
    #[inline]
    pub fn size(self) -> Size {
        use Float::*;
        match self {
            F32 => Size::from_bytes(2),
            F64 => Size::from_bytes(4),
        }
    }

    /// Get the [Alignments] of the [Float].
    pub fn align<C: HasDataLayout>(self, cx: &C) -> Alignments {
        use Float::*;
        let dl = cx.data_layout();

        match self {
            F32 => dl.f32_align,
            F64 => dl.f64_align,
        }
    }
}

/// Represents all of the primitive [AbiRepresentation::Scalar]s that are
/// supported within the ABI.
#[derive(Clone, Copy, Debug)]
pub enum ScalarKind {
    /// An integer scalar.
    Int { kind: Integer, signed: bool },

    /// A float scalar.
    Float { kind: Float },

    /// A pointer primitive scalar value.
    Pointer,
}

/// This range is used to represent the valid range of a scalar value.
/// It has the properties that it is wrapping and inclusive, i.e. if the
/// `start` value is larger than the smaller value, this implies that is
/// greater that `start` until the logical end, and everything up to the `end`
/// is valid as well. For example:
/// ```ignore
/// let range = ValidScalarRange { start: 254, end: 5 }; // `i8` primitive
///
/// /// Sequence is...
///
/// 254 (-2), 255 (-1), 0 (0), 1 (1), 2 (2), 3 (3), 4 (4), 5 (5)
/// ```
///
/// This is used to represent `range!` metadata within LLVM metadata, and
/// possibly other compiler backends that allow for rich range metadata to
/// be emitted. LLVM `range!` metadata reference is at:
///  
/// Language ref: <https://llvm.org/docs/LangRef.html#range-metadata>
///
/// Source: <https://github.com/llvm/llvm-project/blob/main/llvm/lib/IR/ConstantRange.cpp>
#[derive(Clone, Copy)]
pub struct ValidScalarRange {
    /// The minimum value that is valid for this scalar.
    pub start: u128,

    /// The end value of the valid range.
    pub end: u128,
}

impl ValidScalarRange {
    /// Create a "full" range for a valid integer size
    pub fn full(size: Size) -> Self {
        Self { start: 0, end: size.unsigned_int_max() }
    }

    /// Check if a certain value is contained within the
    /// [ValidScalarRange].
    pub fn contains(&self, value: u128) -> bool {
        if self.start > self.end {
            value >= self.start || value <= self.end
        } else {
            value >= self.start && value <= self.end
        }
    }
}

impl fmt::Debug for ValidScalarRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.start > self.end {
            write!(f, "(..<{}) | ({}..)", self.start, self.end)
        } else {
            write!(f, "({}..{})", self.start, self.end)
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Scalar {
    /// The kind of the scalar.
    pub kind: ScalarKind,

    /// The valid range of the scalar, this is used
    /// to provide aditional information about values
    /// that might be encoded as scalars (for efficiency
    /// purposes), but are not actually scalars, e.g. `bool`s
    /// will be encoded as [ScalarKind::Int{..}], and have
    /// a valid range of `0..1`.
    pub valid_range: ValidScalarRange,
}

impl Scalar {
    /// Align the [Scalar] with the current data layout
    /// specification.
    pub fn align<L: HasDataLayout>(&self, ctx: &L) -> Alignments {
        let dl = ctx.data_layout();

        match self.kind {
            ScalarKind::Int { kind, .. } => kind.align(ctx),
            ScalarKind::Float { kind } => kind.align(ctx),
            ScalarKind::Pointer => dl.pointer_align,
        }
    }

    /// Compute the size of the [Scalar].
    pub fn size<L: HasDataLayout>(&self, ctx: &L) -> Size {
        let dl = ctx.data_layout();

        match self.kind {
            ScalarKind::Int { kind, .. } => kind.size(),
            ScalarKind::Float { kind } => kind.size(),
            ScalarKind::Pointer => dl.pointer_size,
        }
    }

    /// Check if the [Scalar] represents a boolean value, i.e. a
    /// [`ScalarKind::Int`] that is an  `i8` with a valid range of `0..1`.
    pub fn is_bool(&self) -> bool {
        matches!(
            self,
            Scalar {
                kind: ScalarKind::Int { kind: Integer::I8, signed: false },
                valid_range: ValidScalarRange { start: 0, end: 1 }
            }
        )
    }
}

/// This defined how values are being represented and are passed by target
/// ABIs in the terms of c-type categories.
#[derive(Debug)]
pub enum AbiRepresentation {
    /// A value that is not represented in memory, but is instead passed
    /// by value. This is used for values that are smaller than a pointer.
    Uninhabited,

    /// A scalar value.
    Scalar(Scalar),

    /// A vector value.
    Vector {
        /// The number of elements in the vector.
        elements: u64,

        /// The kind of the vector.
        kind: Scalar,
    },

    /// An aggregate value.
    Aggregate,
}

impl AbiRepresentation {
    /// Check if the [AbiRepresentation] is a scalar.
    pub fn is_scalar(&self) -> bool {
        matches!(self, AbiRepresentation::Scalar { .. })
    }

    /// Check if the [AbiRepresentation] is uninhabited.
    pub fn is_uninhabited(&self) -> bool {
        matches!(self, AbiRepresentation::Uninhabited)
    }
}

/// An identifier that specifies the address space that some operation
/// should operate on. Special address spaces have an effect on code generation,
/// depending on the target and the address spaces it implements.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AddressSpace(pub u32);

impl AddressSpace {
    /// The default address space, corresponding to data space.
    pub const DATA: Self = AddressSpace(0);
}
