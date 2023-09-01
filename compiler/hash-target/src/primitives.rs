//! Defines primitive types that are used to represent
//! floating-point types, integers, etc. This is located
//! here so that it can be shared across the entire compiler
//! source, and is relevant to computing ABI and type
//! layout information.

use std::fmt;

use crate::{abi::Integer, alignment::Alignments, data_layout::HasDataLayout, size::Size};

/// A primitive floating-point type, either a `f32` or an `f64`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FloatTy {
    F32,
    F64,
}

impl Default for FloatTy {
    fn default() -> Self {
        FloatTy::F64
    }
}

impl FloatTy {
    /// Compute the [Size] of the [FloatTy].
    #[inline]
    pub fn size(self) -> Size {
        use FloatTy::*;
        match self {
            F32 => Size::from_bytes(4),
            F64 => Size::from_bytes(8),
        }
    }

    /// Get the [Alignments] of the [FloatTy].
    pub fn align<C: HasDataLayout>(self, cx: &C) -> Alignments {
        use FloatTy::*;
        let dl = cx.data_layout();

        match self {
            F32 => dl.f32_align,
            F64 => dl.f64_align,
        }
    }
}

impl fmt::Display for FloatTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FloatTy::F32 => write!(f, "f32"),
            FloatTy::F64 => write!(f, "f64"),
        }
    }
}

/// Unsigned integer type variants.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum UIntTy {
    U8,
    U16,
    U32,
    U64,
    U128,
    USize,
    UBig,
}

impl UIntTy {
    /// Get the size of [IntTy] in bytes. Returns [None] for
    /// [UIntTy::UBig] variants
    pub fn size(&self, ptr_size: Size) -> Size {
        match self {
            UIntTy::U8 => Size::from_bytes(1),
            UIntTy::U16 => Size::from_bytes(2),
            UIntTy::U32 => Size::from_bytes(4),
            UIntTy::U64 => Size::from_bytes(8),
            UIntTy::USize => ptr_size,
            UIntTy::U128 => Size::from_bytes(16),
            UIntTy::UBig => panic!("ubig has no defined size"),
        }
    }

    /// Create a new [UIntTy] from a given [Size]. This assumes that
    /// the maximum passed [Size] can be represented as a [`UIntTy::U128`].
    ///
    /// Additionally, this will never use the `usize` type to avoid confusion
    /// between different platforms/targets.
    pub fn from_size(size: Size) -> Self {
        match size.bytes() {
            0..=1 => UIntTy::U8,
            2 => UIntTy::U16,
            3..=4 => UIntTy::U32,
            5..=8 => UIntTy::U64,
            9..=16 => UIntTy::U128,
            _ => unreachable!(),
        }
    }

    /// Function to get the largest possible integer represented within this
    /// type. For sizes `ibig` and `ubig` there is no defined max and so the
    /// function returns [None].
    pub fn max(&self, ptr_size: Size) -> u128 {
        self.size(ptr_size).unsigned_int_max()
    }

    /// Function to get the most minimum integer represented within this
    /// type.
    pub fn min(&self) -> u128 {
        0
    }

    /// Convert the [UIntTy] into a primitive type name
    pub fn to_name(&self) -> &'static str {
        match self {
            UIntTy::U8 => "u8",
            UIntTy::U16 => "u16",
            UIntTy::U32 => "u32",
            UIntTy::U64 => "u64",
            UIntTy::U128 => "u128",
            UIntTy::USize => "usize",
            UIntTy::UBig => "ubig",
        }
    }

    /// Normalise the [UIntTy], i.e. convert the [`UIntTy::USize`] variant
    /// into the normalised type equivalent.
    pub fn normalise(&self, ptr_width: Size) -> Self {
        match self {
            UIntTy::USize => UIntTy::from_size(ptr_width),
            _ => *self,
        }
    }
}

impl From<SIntTy> for UIntTy {
    fn from(value: SIntTy) -> Self {
        match value {
            SIntTy::I8 => UIntTy::U8,
            SIntTy::I16 => UIntTy::U16,
            SIntTy::I32 => UIntTy::U32,
            SIntTy::I64 => UIntTy::U64,
            SIntTy::I128 => UIntTy::U128,
            SIntTy::ISize => UIntTy::USize,
            SIntTy::IBig => UIntTy::UBig,
        }
    }
}

impl From<Integer> for UIntTy {
    fn from(value: Integer) -> Self {
        match value {
            Integer::I8 => UIntTy::U8,
            Integer::I16 => UIntTy::U16,
            Integer::I32 => UIntTy::U32,
            Integer::I64 => UIntTy::U64,
            Integer::I128 => UIntTy::U128,
        }
    }
}

impl From<UIntTy> for IntTy {
    fn from(value: UIntTy) -> Self {
        IntTy::UInt(value)
    }
}

impl fmt::Display for UIntTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_name())
    }
}

/// Signed integer type variants.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum SIntTy {
    I8,
    I16,
    I32,
    I64,
    I128,
    ISize,
    IBig,
}

impl SIntTy {
    /// Get the size of [IntTy] in bytes. Returns [None] for
    /// [UIntTy::UBig] variants
    pub fn size(&self, ptr_width: Size) -> Size {
        match self {
            SIntTy::I8 => Size::from_bytes(1),
            SIntTy::I16 => Size::from_bytes(2),
            SIntTy::I32 => Size::from_bytes(4),
            SIntTy::I64 => Size::from_bytes(8),
            SIntTy::ISize => ptr_width,
            SIntTy::I128 => Size::from_bytes(16),
            SIntTy::IBig => panic!("Cannot get size of IBig"),
        }
    }

    /// Create a new [SIntTy] from a given [Size]. This assumes that
    /// the maximum passed [Size] can be represented as a [`SIntTy::I128`].
    ///
    /// Additionally, this will never use the `usize` type to avoid confusion
    /// between different platforms/targets.
    pub fn from_size(size: Size) -> Self {
        match size.bytes() {
            0..=1 => SIntTy::I8,
            2 => SIntTy::I16,
            3..=4 => SIntTy::I32,
            5..=8 => SIntTy::I64,
            9..=16 => SIntTy::I128,
            _ => unreachable!(),
        }
    }

    /// Function to get the largest possible integer represented within this
    /// type. For sizes `ibig` and `ubig` there is no defined max and so the
    /// function returns [None].
    pub fn max(&self, ptr_size: Size) -> i128 {
        self.size(ptr_size).signed_int_max()
    }

    /// Function to get the most minimum integer represented within this
    /// type. For sizes `ibig` and `ubig` there is no defined minimum and so the
    /// function returns [None].
    pub fn min(&self, ptr_size: Size) -> i128 {
        self.size(ptr_size).signed_int_min()
    }

    /// Convert the [IntTy] into a primitive type name
    pub fn to_name(&self) -> &'static str {
        match self {
            SIntTy::I8 => "i8",
            SIntTy::I16 => "i16",
            SIntTy::I32 => "i32",
            SIntTy::I64 => "i64",
            SIntTy::I128 => "i128",
            SIntTy::ISize => "isize",
            SIntTy::IBig => "ibig",
        }
    }

    /// Normalise the [UIntTy], i.e. convert the [`UIntTy::USize`] variant
    /// into the normalised type equivalent.
    pub fn normalise(&self, ptr_width: Size) -> Self {
        match self {
            SIntTy::ISize => SIntTy::from_size(ptr_width),
            _ => *self,
        }
    }
}

impl From<UIntTy> for SIntTy {
    fn from(value: UIntTy) -> Self {
        match value {
            UIntTy::U8 => SIntTy::I8,
            UIntTy::U16 => SIntTy::I16,
            UIntTy::U32 => SIntTy::I32,
            UIntTy::U64 => SIntTy::I64,
            UIntTy::U128 => SIntTy::I128,
            UIntTy::USize => SIntTy::ISize,
            UIntTy::UBig => SIntTy::IBig,
        }
    }
}

impl From<Integer> for SIntTy {
    fn from(value: Integer) -> Self {
        match value {
            Integer::I8 => SIntTy::I8,
            Integer::I16 => SIntTy::I16,
            Integer::I32 => SIntTy::I32,
            Integer::I64 => SIntTy::I64,
            Integer::I128 => SIntTy::I128,
        }
    }
}

impl From<SIntTy> for IntTy {
    fn from(value: SIntTy) -> Self {
        IntTy::Int(value)
    }
}

impl fmt::Display for SIntTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_name())
    }
}

/// The representation of an integer type.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum IntTy {
    /// Signed integer variant.
    Int(SIntTy),
    /// Unsigned integer variant.
    UInt(UIntTy),
}

impl Default for IntTy {
    fn default() -> Self {
        IntTy::Int(SIntTy::I32)
    }
}

impl IntTy {
    /// Check if the type is is bounded, i.e. not a `ubig` or `ibig` type.
    pub fn is_bounded(&self) -> bool {
        !matches!(self, IntTy::Int(SIntTy::IBig) | IntTy::UInt(UIntTy::UBig))
    }

    /// Convert a [Integer] with signed-ness into a [IntTy]
    pub fn from_integer(integer: Integer, signed: bool) -> Self {
        if signed {
            IntTy::Int(SIntTy::from(integer))
        } else {
            IntTy::UInt(UIntTy::from(integer))
        }
    }

    /// Convert the type into a name.
    pub fn to_name(&self) -> &'static str {
        match self {
            IntTy::Int(ty) => ty.to_name(),
            IntTy::UInt(ty) => ty.to_name(),
        }
    }

    /// Compute the `numeric` min of a given [IntTy] which is the smallest
    /// integer that can be written for the int. The [u128] is used as an
    /// encoding to represent both signed and unsigned integers. In order
    /// to compute the true value of the min, the bias from the `IntTy`
    /// must be applied to the value.
    pub fn numeric_min(&self, ptr_size: Size) -> u128 {
        let size = self.size(ptr_size);

        match self {
            IntTy::Int(_) => size.truncate(size.signed_int_min() as u128),
            IntTy::UInt(_) => 0,
        }
    }

    /// Compute the `numeric` max of a given [IntTy] which is the largest
    /// integer that can be written for the int. The [u128] is used as an
    /// encoding to represent both signed and unsigned integers. In order
    /// to compute the true value of the max, the bias from the `IntTy`
    /// must be applied to the value.
    pub fn numeric_max(&self, ptr_size: Size) -> u128 {
        match self {
            IntTy::Int(val) => val.max(ptr_size) as u128,
            IntTy::UInt(_) => self.size(ptr_size).unsigned_int_max(),
        }
    }

    /// Function to get the size of the integer type in bytes.
    pub fn size(&self, ptr_width: Size) -> Size {
        match self {
            IntTy::Int(ty) => ty.size(ptr_width),
            IntTy::UInt(ty) => ty.size(ptr_width),
        }
    }

    /// Check if the type is signed.
    pub fn is_signed(&self) -> bool {
        matches!(self, IntTy::Int(_))
    }

    /// Check if the type is a pointer integral type, i.e. `isize` or `usize`.
    pub fn is_ptr_sized_integral(self) -> bool {
        matches!(self, IntTy::Int(SIntTy::ISize) | IntTy::UInt(UIntTy::USize))
    }

    /// Check if the type is a [BigInt] variant, i.e. `ibig` or `ubig`.
    pub fn is_bigint(self) -> bool {
        matches!(self, IntTy::Int(SIntTy::IBig) | IntTy::UInt(UIntTy::UBig))
    }

    /// Normalise an [IntTy] by removing "usize" and "isize" variants into
    /// known sized variants.
    pub fn normalise(self, ptr_width: Size) -> Self {
        match self {
            IntTy::Int(ty) => IntTy::Int(ty.normalise(ptr_width)),
            IntTy::UInt(ty) => IntTy::UInt(ty.normalise(ptr_width)),
        }
    }

    /// Convert any [IntTy] into a [UIntTy] variant.
    pub fn to_unsigned(self) -> UIntTy {
        match self {
            IntTy::Int(ty) => ty.into(),
            IntTy::UInt(ty) => ty,
        }
    }

    /// Convert any [IntTy] into a [SIntTy] variant.
    pub fn to_signed(self) -> SIntTy {
        match self {
            IntTy::Int(ty) => ty,
            IntTy::UInt(ty) => ty.into(),
        }
    }
}

impl fmt::Display for IntTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_name())
    }
}

/// A utility wrapper around an [IntTy] that stores the
/// "un-normalised" version of type (i.e. it maybe a `usize` or `isize`),
/// and the original type.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct NormalisedIntTy {
    /// The original type.
    pub original: IntTy,

    /// The normalised type.
    pub normalised: IntTy,
}

impl NormalisedIntTy {
    /// Create a new [NormalisedIntTy] from the given [IntTy] and
    /// [Size].
    pub fn new(original: IntTy, ptr_width: Size) -> Self {
        Self { original, normalised: original.normalise(ptr_width) }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        primitives::{SIntTy, UIntTy},
        size::Size,
    };

    #[test]
    fn test_max_signed_int_value() {
        // Pointer width is always described using a number of bytes
        assert_eq!(SIntTy::ISize.max(Size::from_bytes(8)), isize::MAX as i128);
        assert_eq!(SIntTy::ISize.min(Size::from_bytes(8)), isize::MIN as i128);

        assert_eq!(SIntTy::ISize.max(Size::from_bytes(4)), i32::MAX as i128);
        assert_eq!(SIntTy::ISize.min(Size::from_bytes(4)), i32::MIN as i128);

        // Check that computing the size of each type with pointer widths
        // is consistent.
        assert_eq!(SIntTy::ISize.size(Size::from_bytes(8)), Size::from_bytes(8));
        assert_eq!(SIntTy::ISize.size(Size::from_bytes(4)), Size::from_bytes(4));
    }

    #[test]
    fn test_max_unsigned_int_value() {
        // We don't check `min()` for unsigned since this always
        // returns 0.
        assert_eq!(UIntTy::USize.max(Size::from_bytes(8)), usize::MAX as u128);
        assert_eq!(UIntTy::USize.max(Size::from_bytes(4)), u32::MAX as u128);

        assert_eq!(UIntTy::USize.size(Size::from_bytes(4)), Size::from_bytes(4));
        assert_eq!(UIntTy::USize.size(Size::from_bytes(8)), Size::from_bytes(8));
    }
}
