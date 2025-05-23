//! Contains primitives to define ABIs for various targets. These primitives
//! live in `hash-target` in order to be shared between multiple other crates
//! like `hash-abi` and `hash-codegen`.

use std::fmt;

use crate::{
    alignment::{Alignment, Alignments},
    data_layout::HasDataLayout,
    primitives::{FloatTy, IntTy, SIntTy, UIntTy},
    size::Size,
};

/// ABI representation of an [`ScalarKind::Int`] type. This is
/// agnostic from [SIntTy] and [UIntTy] because it is used to
/// to concretely represent integers that are primitive and are
/// not "machine" dependent in size, i.e. `usize` and `isize` types
/// are converted into the appropriate [Integer] based on the
/// [TargetDataLayout] of the machine.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

    /// Get the [Integer] from the [Size] of the integer.
    pub fn from_size(size: Size) -> Option<Self> {
        match size.bits() {
            8 => Some(Integer::I8),
            16 => Some(Integer::I16),
            32 => Some(Integer::I32),
            64 => Some(Integer::I64),
            128 => Some(Integer::I128),
            _ => None,
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

    /// Finds the smallest [Integer] type which can represent the unsigned
    /// value.
    #[inline]
    #[allow(clippy::match_overlapping_arm)]
    pub fn fit_unsigned(value: u128) -> Integer {
        use Integer::*;

        match value {
            0..=0x0000_0000_0000_00ff => I8,
            0..=0x0000_0000_0000_ffff => I16,
            0..=0x0000_0000_ffff_ffff => I32,
            0..=0xffff_ffff_ffff_ffff => I64,
            _ => I128,
        }
    }

    /// Finds the smallest [Integer] type which can represent the signed
    /// value.
    #[inline]
    #[allow(clippy::match_overlapping_arm)]
    pub fn fit_signed(value: i128) -> Integer {
        use Integer::*;

        match value {
            -0x0000_0000_0000_0080..=0x0000_0000_0000_007f => I8,
            -0x0000_0000_0000_8000..=0x0000_0000_0000_7fff => I16,
            -0x0000_0000_8000_0000..=0x0000_0000_7fff_ffff => I32,
            -0x8000_0000_0000_0000..=0x7fff_ffff_ffff_ffff => I64,
            _ => I128,
        }
    }

    /// Finds the smallest [Integer] with the specified alignment.
    pub fn for_alignment<C: HasDataLayout>(ctx: &C, alignment: Alignment) -> Option<Self> {
        use Integer::*;

        [I8, I16, I32, I64, I128].into_iter().find(|&candidate| {
            alignment == candidate.align(ctx).abi && alignment.bytes() >= candidate.size().bytes()
        })
    }

    /// Create the largest [Integer] type with the given alignment or
    /// less.
    pub fn approximate_alignment<C: HasDataLayout>(ctx: &C, alignment: Alignment) -> Self {
        use Integer::*;

        for candidate in [I128, I64, I32, I16] {
            if alignment >= candidate.align(ctx).abi
                && alignment.bytes() >= candidate.size().bytes()
            {
                return candidate;
            }
        }

        I8
    }

    /// Convert a [UIntTy] into a [Integer].
    pub fn from_unsigned_int_ty<C: HasDataLayout>(ty: UIntTy, ctx: &C) -> Self {
        match ty {
            UIntTy::U8 => Integer::I8,
            UIntTy::U16 => Integer::I16,
            UIntTy::U32 => Integer::I32,
            UIntTy::U64 => Integer::I64,
            UIntTy::U128 => Integer::I128,
            UIntTy::USize => ctx.data_layout().ptr_sized_integer(),
        }
    }

    /// Convert a [SIntTy] into a [Integer].
    pub fn from_signed_int_ty<C: HasDataLayout>(ty: SIntTy, ctx: &C) -> Self {
        match ty {
            SIntTy::I8 => Integer::I8,
            SIntTy::I16 => Integer::I16,
            SIntTy::I32 => Integer::I32,
            SIntTy::I64 => Integer::I64,
            SIntTy::I128 => Integer::I128,
            SIntTy::ISize => ctx.data_layout().ptr_sized_integer(),
        }
    }

    /// Convert an [IntTy] into a [Integer].
    pub fn from_int_ty<C: HasDataLayout>(ty: IntTy, ctx: &C) -> Self {
        match ty {
            IntTy::UInt(ty) => Self::from_unsigned_int_ty(ty, ctx),
            IntTy::Int(ty) => Self::from_signed_int_ty(ty, ctx),
            _ => unreachable!(),
        }
    }
}

/// Represents all of the primitive [AbiRepresentation::Scalar]s that are
/// supported within the ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarKind {
    /// An integer scalar.
    Int { kind: Integer, signed: bool },

    /// A float scalar.
    Float { kind: FloatTy },

    /// A pointer primitive scalar value.
    Pointer(AddressSpace),
}

impl fmt::Display for ScalarKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScalarKind::Int { kind, signed } => {
                let prefix = if *signed { "i" } else { "u" };
                write!(f, "{}{}", prefix, kind.size().bits())
            }
            ScalarKind::Float { kind } => write!(f, "{kind}"),
            ScalarKind::Pointer(_) => write!(f, "<ptr>"),
        }
    }
}

impl ScalarKind {
    /// Compute the [Alignments] of the given [ScalarKind].
    #[inline]
    pub fn align<L: HasDataLayout>(&self, ctx: &L) -> Alignments {
        let dl = ctx.data_layout();

        match self {
            ScalarKind::Int { kind, .. } => kind.align(ctx),
            ScalarKind::Float { kind } => kind.align(ctx),
            ScalarKind::Pointer(_) => dl.pointer_align,
        }
    }

    /// Compute the [Size] of the [ScalarKind].
    #[inline]
    pub fn size<L: HasDataLayout>(&self, ctx: &L) -> Size {
        let dl = ctx.data_layout();

        match self {
            ScalarKind::Int { kind, .. } => kind.size(),
            ScalarKind::Float { kind } => kind.size(),
            ScalarKind::Pointer(_) => dl.pointer_size,
        }
    }

    /// Convert a [UIntTy] into a [ScalarKind].
    pub fn from_unsigned_int_ty<C: HasDataLayout>(ty: UIntTy, ctx: &C) -> Self {
        Self::Int { kind: Integer::from_unsigned_int_ty(ty, ctx), signed: false }
    }

    /// Convert a [SIntTy] into a [ScalarKind].
    pub fn from_signed_int_ty<C: HasDataLayout>(ty: SIntTy, ctx: &C) -> Self {
        Self::Int { kind: Integer::from_signed_int_ty(ty, ctx), signed: true }
    }

    /// Get the [IntTy] of the [ScalarKind].
    ///
    /// ##Note: This will panic if called on a floating point [ScalarKind].
    pub fn int_ty(&self) -> IntTy {
        match self {
            ScalarKind::Int { kind, signed } => {
                if *signed {
                    IntTy::Int(SIntTy::from_size(kind.size()))
                } else {
                    IntTy::UInt(UIntTy::from_size(kind.size()))
                }
            }
            ScalarKind::Pointer(_) => {
                // @@Todo: change this to deal with non-default address spaces.
                IntTy::UInt(UIntTy::USize)
            }
            ScalarKind::Float { .. } => panic!("`int_ty()` called on non-integral ScalarKind"),
        }
    }
}

impl From<FloatTy> for ScalarKind {
    fn from(kind: FloatTy) -> Self {
        ScalarKind::Float { kind }
    }
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
#[derive(Clone, Copy, PartialEq, Eq)]
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

    /// Check if the [ValidScalarRange] is full for the given
    /// [Size] value.
    pub fn is_full_for(&self, size: Size) -> bool {
        let max_value = size.unsigned_int_max();
        debug_assert!(self.start <= max_value && self.end <= max_value);
        self.start == (self.end.wrapping_add(1) & max_value)
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

/// The representation of a scalar-like value within an
/// ABI, what type it is, and what its valid range is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scalar {
    /// The value of the [Scalar] is initialised, and has a known
    /// "valid" range of values.
    Initialised {
        /// The kind of the scalar.
        kind: ScalarKind,

        /// The valid range of the scalar, this is used
        /// to provide additional information about values
        /// that might be encoded as scalars (for efficiency
        /// purposes), but are not actually scalars, e.g. `bool`s
        /// will be encoded as [`ScalarKind::Int`], and have
        /// a valid range of `0..1`.
        valid_range: ValidScalarRange,
    },

    /// The `union` variant is used to represent a scalar within
    /// a union context, i.e. it is not known what the valid range
    /// of the scalar is, and thus there are some less guarantees
    /// about the value of the scalar.
    Union {
        /// Th kind of the scalar
        kind: ScalarKind,
    },
}

impl fmt::Display for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_bool() { write!(f, "bool") } else { write!(f, "{}", self.kind()) }
    }
}

impl Scalar {
    /// Compute the [ScalarKind] of the [Scalar]. This is an infallible
    /// operation for either scalar variant.
    pub fn kind(&self) -> ScalarKind {
        match *self {
            Scalar::Initialised { kind, .. } => kind,
            Scalar::Union { kind } => kind,
        }
    }

    /// Convert the [Scalar] into a union-like [Scalar].
    pub fn to_union(&self) -> Self {
        Scalar::Union { kind: self.kind() }
    }

    /// Check if the [Scalar] is a [`Scalar::Union`].
    pub fn is_union(&self) -> bool {
        matches!(self, Scalar::Union { .. })
    }

    /// Get the [ValidScalarRange] for this [Scalar].
    pub fn valid_range<L: HasDataLayout>(&self, ctx: &L) -> ValidScalarRange {
        match *self {
            Scalar::Initialised { valid_range, .. } => valid_range,
            Scalar::Union { .. } => ValidScalarRange::full(self.size(ctx)),
        }
    }

    /// Get a mutable reference to the [ValidScalarRange] for this [Scalar].
    pub fn valid_range_mut(&mut self) -> &mut ValidScalarRange {
        match self {
            Scalar::Initialised { valid_range, .. } => valid_range,
            Scalar::Union { .. } => panic!("cannot change the valid range of a union"),
        }
    }

    /// Check if this [Scalar] is always valid, i.e. it's [ValidScalarRange]
    /// is total.
    pub fn is_always_valid<L: HasDataLayout>(&self, ctx: &L) -> bool {
        match self {
            Scalar::Initialised { valid_range, .. } => valid_range.is_full_for(self.size(ctx)),
            Scalar::Union { .. } => true,
        }
    }

    /// Align the [Scalar] with the current data layout
    /// specification.
    pub fn align<L: HasDataLayout>(&self, ctx: &L) -> Alignments {
        self.kind().align(ctx)
    }

    /// Compute the size of the [Scalar].
    pub fn size<L: HasDataLayout>(&self, ctx: &L) -> Size {
        self.kind().size(ctx)
    }

    /// Check if the [Scalar] represents a boolean value, i.e. a
    /// [`ScalarKind::Int`] that is an  `i8` with a valid range of `0..1`.
    pub fn is_bool(&self) -> bool {
        matches!(
            self,
            Scalar::Initialised {
                kind: ScalarKind::Int { kind: Integer::I8, signed: false },
                valid_range: ValidScalarRange { start: 0, end: 1 }
            }
        )
    }
}

/// This defined how values are being represented and are passed by target
/// ABIs in the terms of c-type categories.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbiRepresentation {
    /// A value that is not represented in memory, but is instead passed
    /// by value. This is used for values that are smaller than a pointer.
    Uninhabited,

    /// A scalar value.
    Scalar(Scalar),

    /// A pair of two scalar values, this is useful to group
    /// operations or types that produce a pair of values, i.e.
    /// `str` is a pointer to char bytes and an associated length,
    /// thus:
    /// ```ignore
    /// AbiRepresentation::Pair(<...bytes_scalar>..., ...<length_scalar>...)
    /// ```
    Pair(Scalar, Scalar),

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

/// Defines what ABI to use when calling a function.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Abi {
    /// The C ABI.
    C,

    /// The `cold` calling convention, something that
    /// isn't often called and thus should be optimised
    /// for size rather than speed.
    Cold,

    /// The default ABI, which attempts to perform optimisations
    /// that are not possible with the C ABI.
    Hash,
}
