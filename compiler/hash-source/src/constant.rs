//! Hash source interned constant store. This is a data store
//! for interning observed constants within the source file of
//! a program. This is done so that constants don't need to
//! be passed around each stage of the compiler and can just
//! be interned, and accessed when needed.

use std::{
    cmp::Ordering,
    fmt,
    io::Read,
    ops::{IndexMut, Neg},
};

use fnv::FnvBuildHasher;
use hash_target::data_layout::Endian;
// Re-export the "primitives" from the hash-target crate so that everyone can use
// them who depends on `hash-source`
pub use hash_target::primitives::*;
pub use hash_target::size::Size;
use hash_utils::{
    counter,
    dashmap::DashMap,
    fxhash::FxBuildHasher,
    index_vec::{define_index_type, IndexVec},
    lazy_static::lazy_static,
    parking_lot::RwLock,
};
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
        }
    }
}

impl From<BigIntTy> for Identifier {
    fn from(value: BigIntTy) -> Self {
        match value {
            BigIntTy::IBig => IDENTS.ibig,
            BigIntTy::UBig => IDENTS.ubig,
        }
    }
}

impl From<IntTy> for Identifier {
    fn from(value: IntTy) -> Self {
        match value {
            IntTy::Int(ty) => ty.into(),
            IntTy::UInt(ty) => ty.into(),
            IntTy::Big(ty) => ty.into(),
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
            i if i == IDENTS.u8 => Ok(IntTy::UInt(UIntTy::U8)),
            i if i == IDENTS.u16 => Ok(IntTy::UInt(UIntTy::U16)),
            i if i == IDENTS.u32 => Ok(IntTy::UInt(UIntTy::U32)),
            i if i == IDENTS.u64 => Ok(IntTy::UInt(UIntTy::U64)),
            i if i == IDENTS.u128 => Ok(IntTy::UInt(UIntTy::U128)),
            i if i == IDENTS.usize => Ok(IntTy::UInt(UIntTy::USize)),
            i if i == IDENTS.ibig => Ok(IntTy::Big(BigIntTy::IBig)),
            i if i == IDENTS.ubig => Ok(IntTy::Big(BigIntTy::UBig)),
            _ => Err(()),
        }
    }
}

impl TryFrom<Identifier> for FloatTy {
    type Error = ();

    fn try_from(value: Identifier) -> Result<Self, Self::Error> {
        match value {
            i if i == IDENTS.f32 => Ok(FloatTy::F32),
            i if i == IDENTS.f64 => Ok(FloatTy::F64),
            _ => Err(()),
        }
    }
}

impl From<FloatTy> for Identifier {
    fn from(value: FloatTy) -> Self {
        match value {
            FloatTy::F32 => IDENTS.f32,
            FloatTy::F64 => IDENTS.f64,
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
#[derive(Debug, Clone, Copy, PartialEq)]
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
}

impl PartialOrd for FloatConstant {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (&self.value, &other.value) {
            (F64(a), F64(b)) => a.partial_cmp(b),
            (F32(a), F32(b)) => a.partial_cmp(b),
            _ => None,
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

impl fmt::Display for FloatConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            F64(val) => write!(f, "{val}_f64"),
            F32(val) => write!(f, "{val}_f32"),
        }
    }
}

/// Provide implementations for converting primitive floating point types into
/// [FloatConstant]s.
macro_rules! float_const_impl_into {
    ($($ty:ident, $variant: ident);*) => {
        $(
            impl From<$ty> for FloatConstantValue {
                fn from(value: $ty) -> Self {
                    Self::$variant(value)
                }
            }

            impl From<$ty> for FloatConstant {
                fn from(value: $ty) -> Self {
                    Self {
                        value: value.into(),
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

define_index_type! {
    /// Index for [InternedFloat] which is used to index into the [ConstantMap].
    pub struct InternedFloat = u32;

    MAX_INDEX = i32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

impl InternedFloat {
    /// Create a [InternedFloat] from a given [FloatConstant].
    pub fn create(constant: FloatConstant) -> InternedFloat {
        let mut store = CONSTS.floats.write();
        store.push(constant)
    }

    /// Get the underlying type of the interned float.
    pub fn ty(self) -> FloatTy {
        self.map(|constant| constant.ty())
    }

    /// Get the value of the interned float.
    pub fn value(self) -> FloatConstant {
        *CONSTS.floats.read().get(self).unwrap()
    }

    /// Negate the underlying value of the interned float.
    pub fn negate(self) {
        let mut store = CONSTS.floats.write();
        let value = store.get_mut(self).unwrap();
        *value = -*value;
    }

    /// Map the interned float.
    pub fn map<T>(self, f: impl FnOnce(&FloatConstant) -> T) -> T {
        let store = CONSTS.floats.read();
        let constant = store.get(self).unwrap();
        f(constant)
    }
}

impl From<FloatConstant> for InternedFloat {
    fn from(value: FloatConstant) -> Self {
        InternedFloat::create(value)
    }
}

impl fmt::Display for InternedFloat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

// -------------------- Integers --------------------

/// Read a unsigned integer from the given source buffer. This supports buffers
/// of up to 16 bytes in length, and will automaitcally convert it into a
/// `u128`.
///
/// If the desired size should be smaller than a `u128` (which) is often the
/// case, the integer can be "truncated" using [`Size::truncate`].
pub fn read_target_uint(endian: Endian, mut data: &[u8]) -> u128 {
    // This u128 holds an "any-size uint" (since smaller uints can fits in it)
    let mut buf = [0u8; std::mem::size_of::<u128>()];

    // So we do not read exactly 16 bytes into the u128, just the "payload".
    let uint = match endian {
        Endian::Little => {
            data.read(&mut buf).unwrap();
            u128::from_le_bytes(buf)
        }
        Endian::Big => {
            data.read(&mut buf[16 - data.len()..]).unwrap();
            u128::from_be_bytes(buf)
        }
    };

    debug_assert!(data.len() == 0); // We should have consumed the source buffer.
    uint
}

/// Value of the [IntConstant], stores between an `u8` to `u128` value,
/// including signed variants.
#[derive(Debug, Clone, Eq, PartialEq, Hash, Copy)]
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
}

impl IntConstantValue {
    /// Convert the given value into a [u128] provided.
    pub fn as_u128(&self) -> u128 {
        match self {
            Self::I8(inner) => {
                let inner = inner.to_be_bytes();
                let mut bytes = [0; 16];
                bytes[15] = inner[0];
                u128::from_be_bytes(bytes)
            }
            Self::I16(inner) => {
                let inner = inner.to_be_bytes();
                let mut bytes = [0; 16];
                bytes[14..].copy_from_slice(&inner);
                u128::from_be_bytes(bytes)
            }
            Self::I32(inner) => {
                let inner = inner.to_be_bytes();
                let mut bytes = [0; 16];
                bytes[12..].copy_from_slice(&inner);
                u128::from_be_bytes(bytes)
            }
            Self::I64(inner) => {
                let inner = inner.to_be_bytes();
                let mut bytes = [0; 16];
                bytes[8..].copy_from_slice(&inner);
                u128::from_be_bytes(bytes)
            }
            Self::I128(inner) => u128::from_be_bytes(inner.to_be_bytes()),

            // For unsigned values, its fine to just cast them since we're
            // zero extending them anyways...
            Self::U8(inner) => *inner as u128,
            Self::U16(inner) => *inner as u128,
            Self::U32(inner) => *inner as u128,
            Self::U64(inner) => *inner as u128,
            Self::U128(inner) => *inner,
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
            _ => unreachable!("primitive constant can't store values larger than 16 bytes"),
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

impl fmt::Display for IntConstantValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            I8(value) => write!(f, "{value}"),
            I16(value) => write!(f, "{value}"),
            I32(value) => write!(f, "{value}"),
            I64(value) => write!(f, "{value}"),
            I128(value) => write!(f, "{value}"),
            U8(value) => write!(f, "{value}"),
            U16(value) => write!(f, "{value}"),
            U32(value) => write!(f, "{value}"),
            U64(value) => write!(f, "{value}"),
            U128(value) => write!(f, "{value}"),
        }
    }
}

/// Interned literal constant which stores the raw value of the
/// integer and an optional `type ascription` which binds the
/// defined literal value to some ascribed type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IntConstant {
    /// Raw value of the integer.
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
            _ => unreachable!("un-normalised integer type"),
        };

        Self { value, suffix: None }
    }

    /// Create a new [IntConstant] from a given `value` and `ty`.
    ///
    /// N.B. The scalar value assumes that the values are in big
    /// endian order.
    pub fn from_scalar(value: [u8; 16], ty: IntTy, ptr_width: Size) -> Self {
        let size = ty.size(ptr_width);

        // compute the correct slice that we need to use in order to
        // construct the correct integer value.
        let index = (16 - size.bytes()) as usize;
        let mut value = value;

        let value = match ty {
            IntTy::Int(_) => IntConstantValue::from_be_bytes(&mut value[index..], true),
            IntTy::UInt(_) => IntConstantValue::from_be_bytes(&mut value[index..], false),
            _ => unreachable!(),
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

    /// Get the size of the constant.
    pub fn size(&self) -> Size {
        // ##Hack: we always get a normalised type, so we don't need to cate
        // about the size of the constant.
        self.ty().size(Size::ZERO)
    }

    /// Check if the [IntConstant] is `signed` by checking if the specified
    /// suffix matches one of the available signed integer suffixes. If no
    /// suffix is specified, the assumed type of the integer constant is `i32`
    /// and therefore this follows the same assumption.
    pub fn is_signed(&self) -> bool {
        use IntConstantValue::*;
        matches!(self.value, I8(_) | I16(_) | I32(_) | I64(_) | I128(_))
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
            _ => unreachable!(),
        };

        Self { value, suffix: self.suffix }
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
            _ => None,
        }
    }
}

impl fmt::Display for IntConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}_{}", self.value, self.to_int_ty())
    }
}

/// Provide implementations for converting primitive integer types into
/// [IntConstant]s.
macro_rules! int_const_impl_from {
    ($($ty:ty: $variant: ident),* $(,)?) => {
        $(
            impl From<$ty> for IntConstantValue {
                fn from(value: $ty) -> Self {
                    Self::$variant(value)
                }
            }

            impl From<$ty> for IntConstant {
                fn from(value: $ty) -> Self {
                    Self {
                        value: value.into(),
                        suffix: None
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
            impl TryFrom<IntConstantValue> for $ty {
                type Error = ();

                fn try_from(constant: IntConstantValue) -> Result<Self, Self::Error> {
                    match constant {
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
                    }
                }
            }

            impl TryFrom<&IntConstant> for $ty {
                type Error = ();

                fn try_from(constant: &IntConstant) -> Result<Self, Self::Error> {
                    constant.value.try_into()
                }
            }
        )*
    };
}

int_const_impl_into!(i8, i16, i32, i64, isize, i128, u8, u16, u32, u64, usize, u128);

define_index_type! {
    /// Index for [InternedInt] which is used to index into the [ConstantMap].
    pub struct InternedInt = u32;

    MAX_INDEX = i32::max_value() as usize;
    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
}

impl InternedInt {
    /// Create a new [InternedInt] from a given [IntConstant].
    pub fn create(constant: IntConstant) -> Self {
        let mut store = CONSTS.ints.write();
        store.push(constant)
    }

    /// Get the underlying type of the interned float.
    pub fn ty(self) -> IntTy {
        self.map(|constant| constant.ty())
    }

    /// Create a new usize value with the specified `value` and the
    /// current target pointer size.
    pub fn create_usize(value: usize, ptr_width: Size) -> Self {
        let mut constant =
            IntConstant::from_uint(value as u128, UIntTy::USize.normalise(ptr_width));
        constant.suffix = Some(IDENTS.usize); // ##Hack: set the suffix to ensure the `ty` is usize.
        constant.into()
    }

    /// Check if the integer is negative, if the int is unsigned, we
    /// return false.
    pub fn is_negative(self) -> bool {
        self.map(
            |constant| {
                if constant.is_signed() {
                    (constant.value.as_u128() as i128) < 0
                } else {
                    false
                }
            },
        )
    }

    /// Get the value of the integer.
    pub fn value(self) -> IntConstant {
        let store = CONSTS.ints.read();
        store[self].clone()
    }

    /// Get the big-int representation of the value, this is as a
    /// convience method.
    ///
    /// @@Future: remove this!
    pub fn big_value(&self) -> BigInt {
        let value = self.value();

        let sign = if value.is_signed() { Sign::Minus } else { Sign::Plus };
        BigInt::from_bytes_be(sign, &value.value.as_u128().to_be_bytes())
    }

    /// Map a [InternedInt] to a value.
    pub fn map<T>(self, f: impl FnOnce(&IntConstant) -> T) -> T {
        let store = CONSTS.ints.read();
        f(&store[self])
    }

    /// Flip the sign of the underlying constant.
    pub fn negate(self) {
        let mut store = CONSTS.ints.write();
        let value = store.index_mut(self);
        *value = value.clone().neg();
    }

    /// Convert a bias encoded `u128` value with an associated [IntTy] and
    /// convert it into an IntConstantValue.
    pub fn from_u128(value: u128, kind: IntTy, ptr_size: Size) -> Self {
        let size = kind.size(ptr_size).bytes() as usize;
        let is_signed = kind.is_signed();
        let value = IntConstantValue::from_le_bytes(&value.to_le_bytes()[0..size], is_signed);
        Self::create(IntConstant { value, suffix: None })
    }
}

impl From<IntConstant> for InternedInt {
    fn from(value: IntConstant) -> Self {
        InternedInt::create(value)
    }
}

impl fmt::Display for InternedInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

// -------------------- Strings --------------------

counter! {
    name: InternedStr,
    counter_name: STR_LIT_COUNTER,
    visibility: pub,
    method_visibility:,
    derives: (Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd),
}

impl InternedStr {
    /// Get the value of the interned string.
    pub fn value(self) -> &'static str {
        CONSTS.strings.get(&self).unwrap().value()
    }

    /// Intern a string into the [ConstantMap].
    pub fn intern(string: &str) -> InternedStr {
        if let Some(key) = CONSTS.reverse_string_table.get(string) {
            *key
        } else {
            // @@Memory: memory leaks could be avoided/masked by having a wall?
            // copy over the string so that we can insert it into the reverse lookup table
            let value_copy = Box::leak(string.to_owned().into_boxed_str());
            *CONSTS.reverse_string_table.entry(value_copy).or_insert_with(|| {
                let interned = InternedStr::new();
                CONSTS.strings.insert(interned, value_copy);
                interned
            })
        }
    }
}

impl fmt::Display for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl fmt::Debug for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.value())
    }
}

// Utility methods for converting from a InternedString to an InternedStrLit and
// vice versa.

impl From<&str> for InternedStr {
    fn from(string: &str) -> Self {
        InternedStr::intern(string)
    }
}

impl From<String> for InternedStr {
    fn from(string: String) -> Self {
        InternedStr::intern(&string)
    }
}

impl From<InternedStr> for &str {
    fn from(string: InternedStr) -> Self {
        string.value()
    }
}

impl From<InternedStr> for String {
    fn from(string: InternedStr) -> Self {
        String::from(string.value())
    }
}

/// A map containing identifiers that essentially point to a string literal that
/// has been parsed during the tokenisation process. This is so that we don't
/// have to unnecessarily allocate a string multiple times even if it occurs
/// within the source.
#[derive(Debug, Default)]
pub struct ConstantMap {
    /// Where the interned strings are stored.
    strings: DashMap<InternedStr, &'static str, FxBuildHasher>,

    /// Lookup of string references to [InternedStr]. This is the mechansim
    /// behind interning strings and avoiding unnecessary string duplications.
    reverse_string_table: DashMap<&'static str, InternedStr, FnvBuildHasher>,

    /// Float literals store
    floats: RwLock<IndexVec<InternedFloat, FloatConstant>>,

    /// Integer literal store, `char` constants are not stored here
    ints: RwLock<IndexVec<InternedInt, IntConstant>>,
}

lazy_static! {
    pub(super) static ref CONSTS: ConstantMap = ConstantMap::default();
}
