//! Defines primitive types that are used to represent
//! floating-point types, integers, etc. This is located
//! here so that it can be shared across the entire compiler
//! source, and is relevant to computing ABI and type
//! layout information.

use std::fmt;

use num_bigint::BigInt;

use crate::{abi::Integer, alignment::Alignments, data_layout::HasDataLayout, size::Size};

/// A primitive floating-point type, either a `f32` or an `f64`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FloatTy {
    F32,
    F64,
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
    pub fn size(&self, ptr_width: usize) -> Option<Size> {
        match self {
            UIntTy::U8 => Some(Size::from_bytes(1)),
            UIntTy::U16 => Some(Size::from_bytes(2)),
            UIntTy::U32 => Some(Size::from_bytes(4)),
            UIntTy::U64 => Some(Size::from_bytes(8)),
            UIntTy::USize => Some(Size::from_bytes(ptr_width)),
            UIntTy::U128 => Some(Size::from_bytes(16)),
            UIntTy::UBig => None,
        }
    }

    /// Create a new [UnitTy] from a given [Size]. This assumes that
    /// the maximum passed [Size] can be represented as a [UIntTy::U128].
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
    pub fn max(&self, ptr_width: usize) -> Option<BigInt> {
        match self {
            UIntTy::U8 => Some(BigInt::from(u8::MAX)),
            UIntTy::U16 => Some(BigInt::from(u16::MAX)),
            UIntTy::U32 => Some(BigInt::from(u32::MAX)),
            UIntTy::U64 => Some(BigInt::from(u64::MAX)),
            UIntTy::U128 => Some(BigInt::from(u128::MAX)),
            UIntTy::USize => {
                let max = !0u64 >> (64 - (ptr_width * 8));
                Some(BigInt::from(max))
            }
            UIntTy::UBig => None,
        }
    }

    /// Function to get the most minimum integer represented within this
    /// type.
    pub fn min(&self) -> BigInt {
        0.into()
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
    pub fn size(&self, ptr_width: usize) -> Option<Size> {
        match self {
            SIntTy::I8 => Some(Size::from_bytes(1)),
            SIntTy::I16 => Some(Size::from_bytes(2)),
            SIntTy::I32 => Some(Size::from_bytes(4)),
            SIntTy::I64 => Some(Size::from_bytes(8)),
            SIntTy::ISize => Some(Size::from_bytes(ptr_width)),
            SIntTy::I128 => Some(Size::from_bytes(16)),
            SIntTy::IBig => None,
        }
    }

    /// Function to get the largest possible integer represented within this
    /// type. For sizes `ibig` and `ubig` there is no defined max and so the
    /// function returns [None].
    pub fn max(&self, ptr_width: usize) -> Option<BigInt> {
        match self {
            SIntTy::I8 => Some(BigInt::from(i8::MAX)),
            SIntTy::I16 => Some(BigInt::from(i16::MAX)),
            SIntTy::I32 => Some(BigInt::from(i32::MAX)),
            SIntTy::I64 => Some(BigInt::from(i64::MAX)),
            SIntTy::I128 => Some(BigInt::from(i128::MAX)),
            SIntTy::ISize => {
                // convert the size to a signed integer
                let max = (1u64 << (ptr_width * 8 - 1)) - 1;
                Some(BigInt::from(max))
            }
            SIntTy::IBig => None,
        }
    }

    /// Function to get the most minimum integer represented within this
    /// type. For sizes `ibig` and `ubig` there is no defined minimum and so the
    /// function returns [None].
    pub fn min(&self, ptr_width: usize) -> Option<BigInt> {
        match self {
            SIntTy::I8 => Some(BigInt::from(i8::MIN)),
            SIntTy::I16 => Some(BigInt::from(i16::MIN)),
            SIntTy::I32 => Some(BigInt::from(i32::MIN)),
            SIntTy::I64 => Some(BigInt::from(i64::MIN)),
            SIntTy::I128 => Some(BigInt::from(i128::MIN)),
            SIntTy::ISize => {
                let min = (i64::MAX) << ((ptr_width * 8) - 1);
                Some(BigInt::from(min))
            }
            SIntTy::IBig => None,
        }
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

impl IntTy {
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

    /// Function to get the largest possible integer represented within this
    /// type. For sizes `ibig` and `ubig` there is no defined max and so the
    /// function returns [None].
    pub fn max(&self, ptr_width: usize) -> Option<BigInt> {
        match self {
            IntTy::Int(ty) => ty.max(ptr_width),
            IntTy::UInt(ty) => ty.max(ptr_width),
        }
    }

    /// Function to get the most minimum integer represented within this
    /// type. For sizes `ibig` there is no defined minimum and so the
    /// function returns [None].
    pub fn min(&self, ptr_width: usize) -> Option<BigInt> {
        match self {
            IntTy::Int(ty) => ty.min(ptr_width),
            IntTy::UInt(ty) => Some(ty.min()),
        }
    }

    /// Function to get the size of the integer type in bytes.
    pub fn size(&self, ptr_width: usize) -> Option<Size> {
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
    pub fn is_big_sized_integral(self) -> bool {
        matches!(self, IntTy::Int(SIntTy::IBig) | IntTy::UInt(UIntTy::UBig))
    }
}

impl fmt::Display for IntTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_name())
    }
}
