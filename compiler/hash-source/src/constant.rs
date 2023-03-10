//! Hash source interned constant store. This is a data store
//! for interning observed constants within the source file of
//! a program. This is done so that constants don't need to
//! be passed around each stage of the compiler and can just
//! be interned, and accessed when needed.

use std::{cmp::Ordering, fmt, ops::Neg};

use dashmap::DashMap;
use fnv::FnvBuildHasher;
// Re-export the "primitives" from the hash-target crate so that everyone can use
// them who depends on `hash-source`
pub use hash_target::primitives::{FloatTy, IntTy, SIntTy, UIntTy};
use hash_utils::counter;
use lazy_static::lazy_static;
use num_bigint::{BigInt, Sign};
use FloatConstantValue::*;
use IntConstantValue::*;

use crate::identifier::{Identifier, IDENTS};

impl From<UIntTy> for Identifier {
    fn from(value: UIntTy) -> Self {
        match value {
            UIntTy::U8 => IDENTS.u8,
            UIntTy::U16 => IDENTS.u16,
            UIntTy::U32 => IDENTS.u32,
            UIntTy::U64 => IDENTS.u64,
            UIntTy::U128 => IDENTS.u128,
            UIntTy::USize => IDENTS.usize,
            UIntTy::UBig => IDENTS.ubig,
        }
    }
}

impl From<SIntTy> for Identifier {
    fn from(value: SIntTy) -> Self {
        match value {
            SIntTy::I8 => IDENTS.i8,
            SIntTy::I16 => IDENTS.i16,
            SIntTy::I32 => IDENTS.i32,
            SIntTy::I64 => IDENTS.i64,
            SIntTy::I128 => IDENTS.i128,
            SIntTy::ISize => IDENTS.isize,
            SIntTy::IBig => IDENTS.ibig,
        }
    }
}

impl From<IntTy> for Identifier {
    fn from(value: IntTy) -> Self {
        match value {
            IntTy::Int(ty) => ty.into(),
            IntTy::UInt(ty) => ty.into(),
        }
    }
}

impl TryFrom<Identifier> for IntTy {
    type Error = ();

    fn try_from(value: Identifier) -> Result<Self, Self::Error> {
        match value {
            i if i == IDENTS.i8 => Ok(IntTy::Int(SIntTy::I8)),
            i if i == IDENTS.i16 => Ok(IntTy::Int(SIntTy::I16)),
            i if i == IDENTS.i32 => Ok(IntTy::Int(SIntTy::I32)),
            i if i == IDENTS.i64 => Ok(IntTy::Int(SIntTy::I64)),
            i if i == IDENTS.i128 => Ok(IntTy::Int(SIntTy::I128)),
            i if i == IDENTS.isize => Ok(IntTy::Int(SIntTy::ISize)),
            i if i == IDENTS.ibig => Ok(IntTy::Int(SIntTy::IBig)),
            i if i == IDENTS.u8 => Ok(IntTy::UInt(UIntTy::U8)),
            i if i == IDENTS.u16 => Ok(IntTy::UInt(UIntTy::U16)),
            i if i == IDENTS.u32 => Ok(IntTy::UInt(UIntTy::U32)),
            i if i == IDENTS.u64 => Ok(IntTy::UInt(UIntTy::U64)),
            i if i == IDENTS.u128 => Ok(IntTy::UInt(UIntTy::U128)),
            i if i == IDENTS.usize => Ok(IntTy::UInt(UIntTy::USize)),
            i if i == IDENTS.ubig => Ok(IntTy::UInt(UIntTy::UBig)),
            _ => Err(()),
        }
    }
}

// -------------------- Floats --------------------

/// The inner stored value of a [FloatConstant].
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum FloatConstantValue {
    F64(f64),
    F32(f32),
}

impl fmt::Display for FloatConstantValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            F64(inner) => write!(f, "{inner}"),
            F32(inner) => write!(f, "{inner}"),
        }
    }
}

/// Interned float constant which stores the value of the float, and
/// an optional `type ascription` which is a suffix on the literal
/// describing which float kind it is, either being `f32` or `f64`.
#[derive(Debug, Clone, Copy)]
pub struct FloatConstant {
    /// Raw value of the float
    pub value: FloatConstantValue,

    /// If the constant contains a type ascription, as specified
    /// when the constant is declared, e.g. `32.4f64`
    pub suffix: Option<Identifier>,
}

impl FloatConstant {
    /// Create a new [FloatConstant] from the given value and suffix.
    pub fn new(value: FloatConstantValue, suffix: Option<Identifier>) -> Self {
        Self { value, suffix }
    }

    /// Get the value of the float constant as a [f64].
    pub fn as_f64(self) -> f64 {
        match self.value {
            F64(inner) => inner,
            F32(inner) => inner as f64,
        }
    }

    /// Compute the [FloatTy] of the constant.
    pub fn ty(self) -> FloatTy {
        match self.value {
            F64(_) => FloatTy::F64,
            F32(_) => FloatTy::F32,
        }
    }

    /// Perform a conversion from the [FloatConstant] into a specified
    /// [FloatTy].
    fn convert_into(self, ty: FloatTy) -> Self {
        if self.ty() == ty {
            return self;
        }

        match ty {
            FloatTy::F64 => Self::new(F64(self.as_f64()), Some(IDENTS.f64)),
            FloatTy::F32 => Self::new(F32(self.as_f64() as f32), Some(IDENTS.f32)),
        }
    }
}

impl Neg for FloatConstant {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let value = match self.value {
            F64(inner) => F64(-inner),
            F32(inner) => F32(-inner),
        };

        Self { value, suffix: self.suffix }
    }
}

/// Provide implementations for converting primitive floating point types into
/// [FloatConstant]s.
macro_rules! float_const_impl_into {
    ($($ty:ident, $kind: ident);*) => {
        $(
            impl From<$ty> for FloatConstant {
                fn from(value: $ty) -> Self {
                    Self {
                        value: FloatConstantValue::$kind(value),
                        suffix: Some(IDENTS.$ty),
                    }
                }
            }
        )*
    };
}

float_const_impl_into!(f32, F32; f64, F64);

/// A macro to derive `std::ops` on [FloatConstant].
macro_rules! derive_float_ops {
    ($($trt: ident, $op:ident);* $(;)?) => {
        $(
            impl std::ops::$trt for FloatConstant {
                type Output = FloatConstant;

                fn $op(self, rhs: Self) -> Self::Output {
                    match (self.value, rhs.value) {
                        (F32(lhs), F32(rhs)) => Self::new(F32(lhs.$op(rhs)), self.suffix),
                        (F64(lhs), F64(rhs)) => Self::new(F64(lhs.$op(rhs)), self.suffix),
                        _ => unreachable!()
                    }
                }
            }
        )*
    };
}

derive_float_ops!(
    Add, add;
    Sub, sub;
    Mul, mul;
    Div, div;
    Rem, rem;
);

counter! {
    name: InternedFloat,
    counter_name: INTERNED_FLOAT_COUNTER,
    visibility: pub,
    method_visibility:,
}

impl fmt::Display for FloatConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            F64(val) => write!(f, "{val}_f64"),
            F32(val) => write!(f, "{val}_f32"),
        }
    }
}

impl fmt::Display for InternedFloat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", CONSTANT_MAP.lookup_float(*self))
    }
}

// -------------------- Integers --------------------

/// Value of the [IntConstant], this kind be either the `inlined`
/// variant where we just fallback to using `u64` for small sized
/// integer constants, and then in the unlikely scenario of needing
/// more than a [u128] to represent the constant, we will then
/// fallback to [BigInt].
///
/// N.B: Values are always stored and accessed in **Big Endian** format.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum IntConstantValue {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),

    /// For bigger values, we just store a pointer to the `BigInt`
    Big(Box<BigInt>),
}

impl IntConstantValue {
    /// Attempt to convert the given value into a [u128] provided that the
    /// value itself is not [`IntConstantValue::Big`]. If the value is a
    /// big integer, then [`None`] is returned.
    pub fn as_u128(&self) -> Option<u128> {
        match self {
            Self::I8(inner) => {
                let inner = inner.to_be_bytes();
                let mut bytes = [0; 16];
                bytes[15] = inner[0];
                Some(u128::from_be_bytes(bytes))
            }
            Self::I16(inner) => {
                let inner = inner.to_be_bytes();
                let mut bytes = [0; 16];
                bytes[14..].copy_from_slice(&inner);
                Some(u128::from_be_bytes(bytes))
            }
            Self::I32(inner) => {
                let inner = inner.to_be_bytes();
                let mut bytes = [0; 16];
                bytes[12..].copy_from_slice(&inner);
                Some(u128::from_be_bytes(bytes))
            }
            Self::I64(inner) => {
                let inner = inner.to_be_bytes();
                let mut bytes = [0; 16];
                bytes[8..].copy_from_slice(&inner);
                Some(u128::from_be_bytes(bytes))
            }
            Self::I128(inner) => Some(u128::from_be_bytes(inner.to_be_bytes())),

            // For unsigned values, its fine to just cast them since we're
            // zero extending them anyways...
            Self::U8(inner) => Some(*inner as u128),
            Self::U16(inner) => Some(*inner as u128),
            Self::U32(inner) => Some(*inner as u128),
            Self::U64(inner) => Some(*inner as u128),
            Self::U128(inner) => Some(*inner),
            Self::Big(_) => None,
        }
    }

    /// Create a new [IntConstantValue] from little endian ordered bytes.
    pub fn from_le_bytes(bytes: &[u8], signed: bool) -> Self {
        match bytes.len() {
            1 if signed => {
                let mut arr = [0u8; 1];
                arr.copy_from_slice(bytes);

                Self::I8(i8::from_le_bytes(arr))
            }
            1 => Self::U8(bytes[0]),
            2 => {
                let mut arr = [0u8; 2];
                arr.copy_from_slice(bytes);
                Self::I16(i16::from_le_bytes(arr))
            }
            4 => {
                let mut arr = [0u8; 4];
                arr.copy_from_slice(bytes);
                Self::I32(i32::from_le_bytes(arr))
            }
            8 => {
                let mut arr = [0u8; 8];
                arr.copy_from_slice(bytes);
                Self::I64(i64::from_le_bytes(arr))
            }

            16 => {
                let mut arr = [0u8; 16];
                arr.copy_from_slice(bytes);
                Self::I128(i128::from_le_bytes(arr))
            }

            _ => {
                assert!(bytes.len() >= 16, "bigints must be at least 16 bytes");
                Self::Big(Box::new(BigInt::from_signed_bytes_le(bytes)))
            }
        }
    }

    /// Create a new [IntConstantValue] from big endian ordered bytes.
    ///
    /// N.B. The kind of int constant value is determined by the length
    /// of the byte array. If the provided `bytes` is for example 8 bytes
    /// long no sign, then the returned value will be a
    /// [`IntConstantValue::U64`].
    pub fn from_be_bytes(bytes: &mut [u8], signed: bool) -> Self {
        bytes.reverse();
        IntConstantValue::from_le_bytes(bytes, signed)
    }
}

/// A macro to derive `std::ops` on [IntConstantValue].
macro_rules! derive_int_ops {
    ($($trt: ident, $op:ident);* $(;)?) => {
        $(
            impl std::ops::$trt for IntConstant {
                type Output = IntConstant;

                fn $op(self, rhs: Self) -> Self::Output {
                    match (self.value, rhs.value) {
                        (I8(lhs), I8(rhs)) => Self::new(I8(lhs.$op(rhs)), self.suffix),
                        (I16(lhs), I16(rhs)) => Self::new(I16(lhs.$op(rhs)), self.suffix),
                        (I32(lhs), I32(rhs)) => Self::new(I32(lhs.$op(rhs)), self.suffix),
                        (I64(lhs), I64(rhs)) => Self::new(I64(lhs.$op(rhs)), self.suffix),
                        (I128(lhs), I128(rhs)) => Self::new(I128(lhs.$op(rhs)), self.suffix),
                        (U8(lhs), U8(rhs)) => Self::new(U8(lhs.$op(rhs)), self.suffix),
                        (U16(lhs), U16(rhs)) => Self::new(U16(lhs.$op(rhs)), self.suffix),
                        (U32(lhs), U32(rhs)) => Self::new(U32(lhs.$op(rhs)), self.suffix),
                        (U64(lhs), U64(rhs)) => Self::new(U64(lhs.$op(rhs)), self.suffix),
                        (U128(lhs), U128(rhs)) => Self::new(U128(lhs.$op(rhs)), self.suffix),
                        _ => unreachable!()
                    }
                }
            }
        )*
    };
}

derive_int_ops! {
    Add, add;
    Sub, sub;
    Mul, mul;
    Div, div;
    Rem, rem;
    BitAnd, bitand;
    BitOr, bitor;
    BitXor, bitxor;
    Shl, shl;
    Shr, shr
}

/// Interned literal constant which stores the raw value of the
/// integer and an optional `type ascription` which binds the
/// defined literal value to some ascribed type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IntConstant {
    /// Raw value of the integer. This is stored as either a `u128` which can be
    /// directly stored as the value which happens in `99%` of cases, if the
    /// constant is not big enough to store this integer, then we resort to
    /// using [IntConstant
    pub value: IntConstantValue,

    /// If the constant contains a type ascription, as specified
    /// when the constant is declared, e.g. `32u64`
    pub suffix: Option<Identifier>,
}

impl IntConstant {
    /// Create a new [IntConstant] from a given `value` and `ty`.
    pub fn new(value: IntConstantValue, suffix: Option<Identifier>) -> Self {
        Self { value, suffix }
    }

    /// Create a [IntConstant] from a given unsigned integer value and specified
    /// unsigned integer type.
    ///
    /// N.B. This is meant for only converting **unsigned** integers into
    /// constants.
    pub fn from_uint(value: u128, ty: UIntTy) -> Self {
        let value = match ty {
            UIntTy::U8 => IntConstantValue::U8(value as u8),
            UIntTy::U16 => IntConstantValue::U16(value as u16),
            UIntTy::U32 => IntConstantValue::U32(value as u32),
            UIntTy::U64 => IntConstantValue::U64(value as u64),
            UIntTy::U128 => IntConstantValue::U128(value),
            UIntTy::UBig => IntConstantValue::Big(Box::new(BigInt::from(value))),
            _ => unreachable!("un-normalised integer type"),
        };

        Self { value, suffix: None }
    }

    /// Create a [IntConstant] from a given signed integer type.
    ///
    /// N.B. This is meant for only converting **signed** integers into
    /// constants.
    pub fn from_sint(value: i128, ty: SIntTy) -> Self {
        let value = match ty {
            SIntTy::I8 => IntConstantValue::I8(value as i8),
            SIntTy::I16 => IntConstantValue::I16(value as i16),
            SIntTy::I32 => IntConstantValue::I32(value as i32),
            SIntTy::I64 => IntConstantValue::I64(value as i64),
            SIntTy::I128 => IntConstantValue::I128(value),
            SIntTy::IBig => IntConstantValue::Big(Box::new(BigInt::from(value))),
            _ => unreachable!("un-normalised integer type"),
        };

        Self { value, suffix: None }
    }

    /// Create a new [IntConstant] from a given `value` and `ty`.
    ///
    /// N.B. The scalar value assumes that the values are in big
    /// endian order.
    pub fn from_scalar(value: [u8; 16], ty: IntTy, ptr_width: usize) -> Self {
        let size = ty.size(ptr_width).unwrap();

        // compute the correct slice that we need to use in order to
        // construct the correct integer value.
        let index = (16 - size.bytes()) as usize;
        let mut value = value;

        let value = match ty {
            IntTy::Int(_) => IntConstantValue::from_be_bytes(&mut value[index..], true),
            IntTy::UInt(_) => IntConstantValue::from_be_bytes(&mut value[index..], false),
        };

        Self { value, suffix: None }
    }

    /// Function that converts the currently stored [IntConstant]
    /// into the corresponding [IntTy] type that is being used to
    /// store the value.
    fn to_int_ty(&self) -> IntTy {
        use IntConstantValue::*;

        match &self.value {
            I8(_) => IntTy::Int(SIntTy::I8),
            I16(_) => IntTy::Int(SIntTy::I16),
            I32(_) => IntTy::Int(SIntTy::I32),
            I64(_) => IntTy::Int(SIntTy::I64),
            I128(_) => IntTy::Int(SIntTy::I128),
            U8(_) => IntTy::UInt(UIntTy::U8),
            U16(_) => IntTy::UInt(UIntTy::U16),
            U32(_) => IntTy::UInt(UIntTy::U32),
            U64(_) => IntTy::UInt(UIntTy::U64),
            U128(_) => IntTy::UInt(UIntTy::U128),
            Big(value) => {
                if value.sign() == Sign::NoSign {
                    IntTy::UInt(UIntTy::UBig)
                } else {
                    IntTy::Int(SIntTy::IBig)
                }
            }
        }
    }

    /// Compute the normalised [IntTy] of the constant.
    pub fn normalised_ty(&self) -> IntTy {
        self.to_int_ty()
    }

    /// Compute the [IntTy] of the constant.
    pub fn ty(&self) -> IntTy {
        // If the suffix is specified, then we use it as that, this
        // is only specific to the `usize` problem since we don't
        // store specific `usize` variants in the constant since
        // we want to make it platform independent.
        if let Some(suffix) = self.suffix {
            return suffix.try_into().unwrap();
        }

        self.to_int_ty()
    }

    /// Check if the [IntConstant] is `signed` by checking if the specified
    /// suffix matches one of the available signed integer suffixes. If no
    /// suffix is specified, the assumed type of the integer constant is `i32`
    /// and therefore this follows the same assumption.
    pub fn is_signed(&self) -> bool {
        use IntConstantValue::*;

        match self.value {
            I8(_) | I16(_) | I32(_) | I64(_) | I128(_) => true,
            Big(ref t) if t.sign() != Sign::NoSign => true,
            _ => false,
        }
    }
    /// Convert the [IntConstant] into the [IntConstant] with
    /// the specified `ty`.
    fn convert_into(self, ty: IntTy, ptr_width: usize) -> Option<Self> {
        if self.ty() == ty {
            return Some(self);
        }

        let suffix: Identifier = ty.into();
        let this = &self;

        // Re-make the value based on the new type.
        let value = match ty.normalise(ptr_width) {
            IntTy::Int(SIntTy::I8) => IntConstantValue::I8(this.try_into().ok()?),
            IntTy::Int(SIntTy::I16) => IntConstantValue::I16(this.try_into().ok()?),
            IntTy::Int(SIntTy::I32) => IntConstantValue::I32(this.try_into().ok()?),
            IntTy::Int(SIntTy::I64) => IntConstantValue::I64(this.try_into().ok()?),
            IntTy::Int(SIntTy::I128) => IntConstantValue::I128(this.try_into().ok()?),
            IntTy::Int(SIntTy::IBig) => IntConstantValue::Big(Box::new(this.try_into().ok()?)),
            IntTy::UInt(UIntTy::U8) => IntConstantValue::U8(this.try_into().ok()?),
            IntTy::UInt(UIntTy::U16) => IntConstantValue::U16(this.try_into().ok()?),
            IntTy::UInt(UIntTy::U32) => IntConstantValue::U32(this.try_into().ok()?),
            IntTy::UInt(UIntTy::U64) => IntConstantValue::U64(this.try_into().ok()?),
            IntTy::UInt(UIntTy::U128) => IntConstantValue::U128(this.try_into().ok()?),
            IntTy::UInt(UIntTy::UBig) => IntConstantValue::Big(Box::new(this.try_into().ok()?)),
            _ => unreachable!(),
        };

        Some(Self { value, suffix: Some(suffix) })
    }
}

impl Neg for IntConstant {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let value = match self.value {
            I8(t) => I8(-t),
            I16(t) => I16(-t),
            I32(t) => I32(-t),
            I64(t) => I64(-t),
            I128(t) => I128(-t),
            Big(box t) => Big(Box::new(-t)),
            _ => unreachable!(),
        };

        Self { value, suffix: self.suffix }
    }
}

impl From<BigInt> for IntConstant {
    fn from(value: BigInt) -> Self {
        let (sign, mut bytes) = value.to_bytes_be();
        let value = IntConstantValue::from_be_bytes(&mut bytes, sign == Sign::NoSign);

        Self { value, suffix: None }
    }
}

impl PartialOrd for IntConstant {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use IntConstantValue::*;

        // We need to get the value from the constant, and then
        // perform a comparison on the two values.
        match (&self.value, &other.value) {
            (I8(left), I8(right)) => Some(left.cmp(right)),
            (I16(left), I16(right)) => Some(left.cmp(right)),
            (I32(left), I32(right)) => Some(left.cmp(right)),
            (I64(left), I64(right)) => Some(left.cmp(right)),
            (I128(left), I128(right)) => Some(left.cmp(right)),
            (U8(left), U8(right)) => Some(left.cmp(right)),
            (U16(left), U16(right)) => Some(left.cmp(right)),
            (U32(left), U32(right)) => Some(left.cmp(right)),
            (U64(left), U64(right)) => Some(left.cmp(right)),
            (U128(left), U128(right)) => Some(left.cmp(right)),
            (Big(left), Big(right)) => Some(left.cmp(right)),
            _ => None,
        }
    }
}

/// Provide implementations for converting primitive integer types into
/// [IntConstant]s.
macro_rules! int_const_impl_from {
    ($($ty:ident: $variant: ident),* $(,)?) => {
        $(
            impl From<$ty> for IntConstant {
                fn from(value: $ty) -> Self {
                    Self {
                        value: IntConstantValue::$variant(value),
                        suffix: Some(IDENTS.$ty)
                    }
                }
            }
        )*
    };
}

int_const_impl_from!(
    i8: I8,
    i16: I16,
    i32: I32,
    i64: I64,
    i128: I128,
    u8: U8,
    u16: U16,
    u32: U32,
    u64: U64,
    u128: U128,
);

// /// Provide implementations for converting [IntConstant]s into primitive
// /// integer types. This uses the system defined sizes for the primitive
// /// integer types, and should not be used to reliably convert into target
// /// sized integers.
macro_rules! int_const_impl_into {
    ($($ty:ident),* $(,)?) => {
        $(
            impl TryFrom<&IntConstant> for $ty {
                type Error = ();

                fn try_from(constant: &IntConstant) -> Result<Self, Self::Error> {
                    use IntConstantValue::*;

                    match constant.value {
                        I8(value) => value.try_into().map_err(|_| ()),
                        I16(value) => value.try_into().map_err(|_| ()),
                        I32(value) => value.try_into().map_err(|_| ()),
                        I64(value) => value.try_into().map_err(|_| ()),
                        I128(value) => value.try_into().map_err(|_| ()),
                        U8(value) => value.try_into().map_err(|_| ()),
                        U16(value) => value.try_into().map_err(|_| ()),
                        U32(value) => value.try_into().map_err(|_| ()),
                        U64(value) => value.try_into().map_err(|_| ()),
                        U128(value) => value.try_into().map_err(|_| ()),
                        Big(box ref value) => value.clone().try_into().map_err(|_| ()),
                    }
                }
            }
        )*
    };
}

int_const_impl_into!(i8, i16, i32, i64, isize, i128, u8, u16, u32, u64, usize, u128, BigInt);

counter! {
    name: InternedInt,
    counter_name: INTERNED_INT_COUNTER,
    visibility: pub,
    method_visibility:,
}

impl fmt::Display for IntConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.value {
            // We want to snip the value from the `total` value since we don't care about the
            // rest...
            I8(value) => write!(f, "{value}_i8"),
            I16(value) => write!(f, "{value}_i16"),
            I32(value) => write!(f, "{value}_i32"),
            I64(value) => write!(f, "{value}_i64"),
            I128(value) => write!(f, "{value}_i128"),
            U8(value) => write!(f, "{value}_u8"),
            U16(value) => write!(f, "{value}_u16"),
            U32(value) => write!(f, "{value}_u32"),
            U64(value) => write!(f, "{value}_u64"),
            U128(value) => write!(f, "{value}_u128"),
            Big(value) => write!(f, "{value}"),
        }
    }
}

impl fmt::Display for InternedInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", CONSTANT_MAP.lookup_int(*self))
    }
}

/// Convert a given `i128` value with an associated [IntTy] and convert
/// it into an IntConstantValue.
pub fn u128_to_int_const(value: u128, kind: IntTy, ptr_width: usize) -> InternedInt {
    let size = kind.size(ptr_width).unwrap().bytes() as usize;
    let is_signed = kind.is_signed();

    let value = IntConstantValue::from_le_bytes(&value.to_le_bytes()[0..size], is_signed);
    CONSTANT_MAP.create_int(IntConstant { value, suffix: None })
}

// -------------------- Strings --------------------

counter! {
    name: InternedStr,
    counter_name: STR_LIT_COUNTER,
    visibility: pub,
    method_visibility:,
    derives: (Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd),
}

impl fmt::Display for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", CONSTANT_MAP.lookup_string(*self))
    }
}

impl fmt::Debug for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", CONSTANT_MAP.lookup_string(*self))
    }
}

// Utility methods for converting from a InternedString to an InternedStrLit and
// vice versa.

impl From<&str> for InternedStr {
    fn from(string: &str) -> Self {
        CONSTANT_MAP.create_string(string)
    }
}

impl From<String> for InternedStr {
    fn from(string: String) -> Self {
        CONSTANT_MAP.create_string(&string)
    }
}

impl From<InternedStr> for &str {
    fn from(string: InternedStr) -> Self {
        CONSTANT_MAP.lookup_string(string)
    }
}

impl From<InternedStr> for String {
    fn from(string: InternedStr) -> Self {
        String::from(CONSTANT_MAP.lookup_string(string))
    }
}

/// A map containing identifiers that essentially point to a string literal that
/// has been parsed during the tokenisation process. This is so that we don't
/// have to unnecessarily allocate a string multiple times even if it occurs
/// within the source.
#[derive(Debug, Default)]
pub struct ConstantMap {
    /// Where the interned strings are stored.
    string_table: DashMap<InternedStr, &'static str, FnvBuildHasher>,

    /// It's useful to lookup [InternedStr] from a raw string.
    reverse_string_table: DashMap<&'static str, InternedStr, FnvBuildHasher>,

    /// Float literals store
    float_table: DashMap<InternedFloat, FloatConstant, FnvBuildHasher>,

    /// Integer literal store, `char` constants are not stored here
    int_table: DashMap<InternedInt, IntConstant, FnvBuildHasher>,
}

lazy_static! {
    pub static ref CONSTANT_MAP: ConstantMap = ConstantMap::default();
}

impl ConstantMap {
    /// Add a new string to the map, this will add an additional entry even if
    /// the string is already within the map.
    pub fn create_string(&self, value: &str) -> InternedStr {
        if let Some(key) = self.reverse_string_table.get(value) {
            *key
        } else {
            // @@Memory: memory leaks could be avoided/masked by having a wall?
            // copy over the string so that we can insert it into the reverse lookup table
            let value_copy = Box::leak(value.to_owned().into_boxed_str());
            *self.reverse_string_table.entry(value_copy).or_insert_with(|| {
                let interned = InternedStr::new();
                self.string_table.insert(interned, value_copy);
                interned
            })
        }
    }

    /// Get the [String] behind the [InternedStr]
    pub fn lookup_string(&self, ident: InternedStr) -> &'static str {
        self.string_table.get(&ident).unwrap().value()
    }

    /// Create a `f64` [FloatConstant] within the [ConstantMap]
    pub fn create_f64_float(&self, value: f64, suffix: Option<Identifier>) -> InternedFloat {
        let constant = FloatConstant { value: FloatConstantValue::F64(value), suffix };
        self.create_float(constant)
    }

    /// Create a `f32` [FloatConstant] within the [ConstantMap]
    pub fn create_f32_float(&self, value: f32, suffix: Option<Identifier>) -> InternedFloat {
        let constant = FloatConstant { value: FloatConstantValue::F32(value), suffix };
        self.create_float(constant)
    }

    /// Create a [FloatConstant] within the [ConstantMap]
    pub fn create_float(&self, constant: FloatConstant) -> InternedFloat {
        let ident = InternedFloat::new();
        self.float_table.insert(ident, constant);

        ident
    }

    /// Get the [FloatConstant] behind the [InternedFloat]
    pub fn lookup_float(&self, id: InternedFloat) -> FloatConstant {
        *self.float_table.get(&id).unwrap().value()
    }

    /// Perform a transformation on the [FloatConstant] behind the
    /// [InternedFloat] without making a copy of the original value.
    pub fn map_float<T>(&self, id: InternedFloat, f: impl FnOnce(&FloatConstant) -> T) -> T {
        let lookup_value = self.float_table.get(&id).unwrap();
        f(lookup_value.value())
    }

    /// Perform a negation operation on an [InternedFloat].
    pub fn negate_float(&self, id: InternedFloat) {
        self.float_table.alter(&id, |_, value| -value);
    }

    /// Adjust the underlying [FloatConstant] into a specified
    /// float type.
    pub fn adjust_float(&self, id: InternedFloat, ty: FloatTy) {
        self.float_table.alter(&id, |_, value| value.convert_into(ty));
    }

    /// Create a [IntConstant] within the [ConstantMap].
    pub fn create_int(&self, constant: IntConstant) -> InternedInt {
        let ident = InternedInt::new();

        // Insert the entries into the map and the reverse-lookup map
        self.int_table.insert(ident, constant);
        ident
    }

    /// Get the [IntConstant] behind the [InternedInt]
    pub fn lookup_int(&self, id: InternedInt) -> IntConstant {
        let lookup_value = self.int_table.get(&id).unwrap();
        lookup_value.value().clone()
    }

    /// Perform a transformation on the [IntConstant] behind the [InternedInt]
    /// without making a copy of the original value.
    pub fn map_int<T>(&self, id: InternedInt, f: impl FnOnce(&IntConstant) -> T) -> T {
        let lookup_value = self.int_table.get(&id).unwrap();
        f(lookup_value.value())
    }

    /// Adjust the underlying [IntConstant] into a specified integer type.
    pub fn adjust_int(&self, id: InternedInt, ty: IntTy, ptr_width: usize) {
        self.int_table.alter(&id, |_, item| {
            item.convert_into(ty, ptr_width)
                .unwrap_or_else(|| panic!("failed to convert `{id}` to `{ty}`"))
        })
    }

    /// Perform a negation operation on an [InternedInt].
    pub fn negate_int(&self, id: InternedInt) {
        self.int_table.alter(&id, |_, value| -value);
    }
}

#[cfg(test)]
mod tests {
    use hash_target::{
        primitives::{SIntTy, UIntTy},
        size::Size,
    };
    use num_bigint::BigInt;

    #[test]
    fn test_max_signed_int_value() {
        // Pointer width is always described using a number of bytes
        assert_eq!(SIntTy::ISize.max(8), Some(BigInt::from(isize::MAX)));
        assert_eq!(SIntTy::ISize.min(8), Some(BigInt::from(isize::MIN)));

        assert_eq!(SIntTy::ISize.max(4), Some(BigInt::from(i32::MAX)));
        assert_eq!(SIntTy::ISize.min(4), Some(BigInt::from(i32::MIN)));

        // Check that computing the size of each type with pointer widths
        // is consistent.
        assert_eq!(SIntTy::ISize.size(8), Some(Size::from_bytes(8)));
        assert_eq!(SIntTy::ISize.size(4), Some(Size::from_bytes(4)));
    }

    #[test]
    fn test_max_unsigned_int_value() {
        // We don't check `min()` for unsigned since this always
        // returns 0.
        assert_eq!(UIntTy::USize.max(8), Some(BigInt::from(usize::MAX)));
        assert_eq!(UIntTy::USize.max(4), Some(BigInt::from(u32::MAX)));

        assert_eq!(UIntTy::USize.size(4), Some(Size::from_bytes(4)));
        assert_eq!(UIntTy::USize.size(8), Some(Size::from_bytes(8)));
    }
}
