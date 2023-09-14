//! Defines the representation used for constants within the
//! Hash IR. This representation allows for arbitrary constants
//! to be represented, whether it is a simple scalar value or a
//! complex aggregate value.

use core::fmt;
use std::{
    borrow::Cow,
    num::NonZeroU8,
    ops::{Deref, DerefMut},
};

use hash_source::constant::{read_target_uint, IntConstant, IntConstantValue, InternedStr};
use hash_storage::{static_single_store, store::statics::StoreId};
use hash_target::{
    alignment::Alignment, data_layout::HasDataLayout, primitives::IntTy, size::Size,
};
use hash_tir::lits::Lit;
use hash_utils::derive_more::Constructor;

use crate::{
    ir_stores,
    ty::{IrTy, IrTyId, Mutability, COMMON_IR_TYS},
};

/// A [Const] represents a constant value within the Hash IR. This can
/// be anything that can be represented as a constant, including ABI scalars,
/// ADTs, slices, and arrays. This representation is intended to be used
/// throughout the compiler from TIR, IR and potentially the VM as well.
///
/// @@Future: There should be a well defined translation procedure from a
/// [Const] into the equivalent TIR value, this will be used for communicating
/// results from compile time evaluation back into the type system. Furthermore,
/// the VM will likely operate on this representation to simplify communication
/// of values/results
#[derive(Clone, Copy, Debug, Constructor, PartialEq, Eq, Hash)]
pub struct Const {
    /// The type of the constant value.
    ty: IrTyId,

    /// The kind of constant that is stored.
    pub kind: ConstKind,
}

impl Const {
    /// Create a ZST constant.
    pub fn zero() -> Self {
        Self::new(COMMON_IR_TYS.unit, ConstKind::Zero)
    }

    /// Create a ZST constant which is of `zero` size with
    /// a type.
    pub fn zst(ty: IrTyId) -> Self {
        Self::new(ty, ConstKind::Zero)
    }

    /// Check if the [Const] is a zero value.
    pub fn is_zero(&self) -> bool {
        matches!(self.kind, ConstKind::Zero)
    }

    /// Get the type of the constant.
    pub fn ty(&self) -> IrTyId {
        self.ty
    }

    /// Get the [ConstKind] of the [Const].
    pub fn kind(&self) -> ConstKind {
        self.kind
    }

    /// Check if the constant is switchable.
    pub fn is_switchable(&self) -> bool {
        matches!(self.kind, ConstKind::Scalar(_) if self.ty.borrow().is_switchable())
    }

    /// Get the backing [AllocId] if the constant is an allocation.
    ///
    /// ##Note: Panics if the constant does not have a baking allocation.
    pub fn alloc(&self) -> AllocId {
        match self.kind {
            ConstKind::Alloc { alloc, .. } => alloc,
            _ => panic!("Const is not an allocation"),
        }
    }

    /// Create a new [Const] from a integer with the given type.
    pub fn from_scalar_like<C: HasDataLayout>(value: u128, ty: IrTyId, ctx: &C) -> Self {
        let kind = match ty.value() {
            // @@FixMe: we're converting from one to another... seems dumb!
            IrTy::Bool => ConstKind::Scalar(Scalar::from_bool(value != 0)),
            _ => {
                let size = IntTy::from(ty.value()).size(ctx.data_layout().pointer_size);
                ConstKind::Scalar(Scalar::from_uint(value, size))
            }
        };

        Const { ty, kind }
    }

    /// Create a boolean constant.
    pub fn bool(value: bool) -> Self {
        Self::new(COMMON_IR_TYS.bool, ConstKind::Scalar(Scalar::from_bool(value)))
    }

    /// Create a character constant.
    pub fn char(value: char) -> Self {
        Self::new(COMMON_IR_TYS.char, ConstKind::Scalar(Scalar::from(value)))
    }

    /// Create a new [Const] which represents a `usize`.
    pub fn usize<C: HasDataLayout>(value: u64, ctx: &C) -> Self {
        let kind = ConstKind::Scalar(Scalar::from_usize(value, ctx));
        Self::new(COMMON_IR_TYS.usize, kind)
    }
}

macro_rules! const_from_ty_impl {
    ($($ty:ident),*) => {
        $(
            impl From<$ty> for Const {
                fn from(value: $ty) -> Self {
                    Const::new(COMMON_IR_TYS.$ty, ConstKind::Scalar(Scalar::from(value)))
                }
            }
        )*
    };
}

const_from_ty_impl!(f32, f64, char);

/// The kind of constants that can be represented within the Hash IR.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ConstKind {
    /// Exotic constant, that has no size, effectively a unit.
    Zero,

    /// A constant scalar value.
    Scalar(Scalar),

    /// A pair is only used to represent `str` constants, which is the interned
    /// string allocation, and the length. It is equivalent to the `Abi::Pair`
    /// representation.
    Pair {
        /// The data pointer of the slice. This is represented as just
        /// being an
        data: InternedStr,

        /// The length of the slice.
        len: Scalar,
    },

    /// An allocated constant value, this is used to represent everything
    /// that is non-scalar, including slices, ADTs and arrays.
    Alloc {
        /// The offset into the given allocation that is being used.
        offset: Size,

        /// The allocation itself.
        alloc: AllocId,
    },
}

impl ConstKind {
    /// Create a [ConstKind] from a TIR literal.
    pub fn from_lit<C: HasDataLayout>(lit: Lit, ctx: &C) -> Self {
        match lit {
            Lit::Int(int) => ConstKind::Scalar(Scalar::from(int.value())),
            Lit::Float(float) => ConstKind::Scalar(Scalar::from(float.value())),
            Lit::Str(str) => {
                let data = str.interned_value();
                ConstKind::Pair { data, len: Scalar::from_usize(data.len() as u64, ctx) }
            }
            Lit::Char(ch) => ConstKind::Scalar(Scalar::from(ch.value())),
        }
    }
}

/// A scalar value. [Scalar]s are used to represent all integer, characters, and
/// floating point values, as well as integers. The largest scalar value is
/// 128bits, i.e. a `u128` or `i128`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(packed)]
pub struct Scalar {
    /// The buffer of the scalar, up to 16bytes.
    value: u128,

    /// The size of the buffer that is being used. It
    /// cannot be zero.
    size: NonZeroU8,
}

impl Scalar {
    pub const TRUE: Scalar = Scalar { value: 1_u128, size: NonZeroU8::new(1).unwrap() };
    pub const FALSE: Scalar = Scalar { value: 0_u128, size: NonZeroU8::new(1).unwrap() };

    /// Compute the [Size] of the [Scalar].
    pub fn size(&self) -> Size {
        Size::from_bytes(self.size.get() as u64)
    }

    /// Create a new [Scalar] from a usize for the target
    /// architecture.
    pub fn from_usize<C: HasDataLayout>(value: u64, ctx: &C) -> Self {
        Self::try_from_uint(value, ctx.data_layout().pointer_size)
            .unwrap_or_else(|| panic!("usize is too large for the target architecture"))
    }

    /// Internal check to ensure that the [Scalar] is not in an invalid state.
    ///
    /// ##Note: this function will check whether the specified `size` of the
    /// scalar is enough to hold the value.
    #[inline(always)]
    fn check(&self) {
        debug_assert_eq!(
            self.size().truncate(self.value),
            { self.value },
            "Scalar value is too large for the specified size"
        )
    }

    #[inline]
    pub fn to_bits(self, target_size: Size) -> Result<u128, Size> {
        assert_ne!(target_size.bytes(), 0, "you should never look at the bits of a ZST");
        if target_size.bytes() == u64::from(self.size.get()) {
            self.check();
            Ok(self.value)
        } else {
            Err(self.size())
        }
    }

    pub fn assert_bits(self, target_size: Size) -> u128 {
        self.to_bits(target_size)
            .unwrap_or_else(|_| panic!("assertion failed: {self:?} fits {target_size:?}"))
    }

    /// Attempt to convert an un-signed integer value into a [Scalar].
    pub fn try_from_uint(i: impl Into<u128>, size: Size) -> Option<Self> {
        let value = i.into();

        if size.truncate(value) == value {
            Some(Self { value, size: NonZeroU8::new(size.bytes() as u8).unwrap() })
        } else {
            None
        }
    }

    /// Convert an unsigned integer value into a [Scalar].
    #[inline]
    pub fn from_uint(i: impl Into<u128>, size: Size) -> Self {
        Self::try_from_uint(i, size).unwrap_or_else(|| {
            panic!("Integer value is too large for the specified size: {}", size.bytes())
        })
    }

    /// Attempt to convert a signed integer value into a [Scalar].
    pub fn try_from_int(i: impl Into<i128>, size: Size) -> Option<Self> {
        let value = i.into();
        let truncated = size.truncate(value as u128);

        if size.sign_extend(truncated) as i128 == value {
            Some(Self { value: truncated, size: NonZeroU8::new(size.bytes() as u8).unwrap() })
        } else {
            None
        }
    }

    /// Convert an unsigned integer value into a [Scalar].
    #[inline]
    pub fn from_int(i: impl Into<i128>, size: Size) -> Self {
        Self::try_from_int(i, size).unwrap_or_else(|| {
            panic!("Integer value is too large for the specified size: {}", size.bytes())
        })
    }

    /// Create a new [Scalar] from a boolean value.
    #[inline]
    pub fn from_bool(value: bool) -> Self {
        if value {
            Self::TRUE
        } else {
            Self::FALSE
        }
    }

    /// Convert the [Scalar] into a [f32].
    pub fn to_f32(&self) -> f32 {
        f32::try_from(*self).unwrap()
    }

    /// Convert the [Scalar] into a [f64].
    pub fn to_f64(&self) -> f64 {
        f64::try_from(*self).unwrap()
    }
}

impl From<bool> for Scalar {
    fn from(value: bool) -> Self {
        Self {
            value: value as u128,
            size: NonZeroU8::new(std::mem::size_of::<bool>() as u8).unwrap(),
        }
    }
}

impl TryFrom<Scalar> for bool {
    type Error = Size;
    #[inline]
    fn try_from(value: Scalar) -> Result<Self, Self::Error> {
        value.to_bits(Size::from_bytes(1)).and_then(|u| match u {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(Size::from_bytes(1)),
        })
    }
}

impl From<char> for Scalar {
    fn from(value: char) -> Self {
        Self {
            value: value as u128,
            size: NonZeroU8::new(std::mem::size_of::<char>() as u8).unwrap(),
        }
    }
}

impl TryFrom<Scalar> for char {
    type Error = ();

    fn try_from(value: Scalar) -> Result<Self, Self::Error> {
        let Ok(val) = value.to_bits(Size::from_bytes(std::mem::size_of::<char>())) else {
            return Err(());
        };

        match char::from_u32(val.try_into().unwrap()) {
            Some(c) => Ok(c),
            None => Err(()),
        }
    }
}

impl From<IntConstant> for Scalar {
    fn from(value: IntConstant) -> Self {
        let size = value.size();

        match value.value {
            IntConstantValue::I8(val) => Scalar::from_int(val, size),
            IntConstantValue::I16(val) => Scalar::from_int(val, size),
            IntConstantValue::I32(val) => Scalar::from_int(val, size),
            IntConstantValue::I64(val) => Scalar::from_int(val, size),
            IntConstantValue::I128(val) => Scalar::from_int(val, size),
            IntConstantValue::U8(val) => Scalar::from_uint(val, size),
            IntConstantValue::U16(val) => Scalar::from_uint(val, size),
            IntConstantValue::U32(val) => Scalar::from_uint(val, size),
            IntConstantValue::U64(val) => Scalar::from_uint(val, size),
            IntConstantValue::U128(val) => Scalar::from_uint(val, size),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Constructor)]
pub struct ScalarInt {
    /// The underlying scalar value.
    data: Scalar,

    /// Whether the integer is signed or not.
    ty: IntTy,
}

impl fmt::Display for ScalarInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let size = self.data.size();
        let bits = self.data.to_bits(size).unwrap();

        if self.ty.is_signed() {
            let value = size.sign_extend(bits) as i128;
            write!(f, "{}_{}", value, self.ty.normalise(size))
        } else {
            write!(f, "{}_{}", bits, self.ty.normalise(size))
        }
    }
}

impl From<f32> for Scalar {
    fn from(value: f32) -> Self {
        Self {
            value: value.to_bits() as u128,
            size: NonZeroU8::new(std::mem::size_of::<f32>() as u8).unwrap(),
        }
    }
}

impl TryFrom<Scalar> for f32 {
    type Error = Size;

    fn try_from(value: Scalar) -> Result<Self, Self::Error> {
        value
            .to_bits(Size::from_bytes(std::mem::size_of::<f32>()))
            .map(|u| f32::from_bits(u as u32))
    }
}

impl From<f64> for Scalar {
    fn from(value: f64) -> Self {
        Self {
            value: value.to_bits() as u128,
            size: NonZeroU8::new(std::mem::size_of::<f64>() as u8).unwrap(),
        }
    }
}

impl TryFrom<Scalar> for f64 {
    type Error = Size;

    fn try_from(value: Scalar) -> Result<Self, Self::Error> {
        value
            .to_bits(Size::from_bytes(std::mem::size_of::<f64>()))
            .map(|u| f64::from_bits(u as u64))
    }
}

/// An [Alloc] represents a single allocation slot which contains the actual
/// data, alignment, and mutability of the allocation.
#[derive(Clone, Debug)]
pub struct Alloc<Buf = Box<[u8]>> {
    /// The buffer that is being used to store the value.
    buf: Buf,

    /// The alignment of the buffer.
    align: Alignment,

    /// The mutability of the allocation.
    ///
    /// ##Note: this is still not entirely figured out in the language. Perhaps, variables
    /// that are 'static' can be mutable, and everything else is immutable.
    mutability: Mutability,
}

/// Used for indexing into an [Alloc] by specifying the
/// offset and size of the range.
#[derive(Clone, Copy, Constructor)]
pub struct AllocRange {
    /// The offset into the allocation.
    pub start: Size,

    /// The size of the range.
    pub size: Size,
}

impl AllocRange {
    /// Get the end of the [AllocRange].
    pub fn end(&self) -> Size {
        self.start + self.size
    }
}

pub trait AllocBuf: Clone + fmt::Debug + Deref<Target = [u8]> + DerefMut<Target = [u8]> {
    /// Create a new allocation buffer from the given bytes.
    fn from_bytes<'a>(slice: impl Into<Cow<'a, [u8]>>, align: Alignment) -> Self;
}

impl AllocBuf for Box<[u8]> {
    fn from_bytes<'a>(slice: impl Into<Cow<'a, [u8]>>, _align: Alignment) -> Self {
        slice.into().into_owned().into_boxed_slice()
    }
}

impl<Buf: AllocBuf> Alloc<Buf> {
    /// Creates an [Alloc] initialized by the given bytes.
    pub fn from_bytes<'a>(
        slice: impl Into<Cow<'a, [u8]>>,
        align: Alignment,
        mutability: Mutability,
    ) -> Self {
        let buf = Buf::from_bytes(slice, align);
        Self { buf, align, mutability }
    }

    /// Create an immutable [Alloc] initialized by the given bytes with
    /// alignment of [`Alignment::ONE`].
    pub fn from_bytes_immutable<'a>(slice: impl Into<Cow<'a, [u8]>>) -> Self {
        Self::from_bytes(slice, Alignment::ONE, Mutability::Immutable)
    }

    #[inline]
    pub fn read_bytes(&self, range: AllocRange) -> &[u8] {
        &self.buf[range.start.bytes_usize()..range.end().bytes_usize()]
    }

    /// Read a [Scalar] from the given [Alloc].
    ///
    /// @@FixMe: Add some kind of errors for this?
    pub fn read_scalar<C: HasDataLayout>(&self, range: AllocRange, ctx: &C) -> Scalar {
        let data = self.read_bytes(range);
        let int = read_target_uint(ctx.data_layout().endian, data).unwrap();

        // Finally, convert it into a scalar from the integer and size.
        Scalar::from_uint(int, range.size)
    }

    /// Get the length of the [Alloc].
    pub fn len(&self) -> usize {
        self.buf.len()
    }

    /// Check if the allocation is empty.
    pub fn is_empty(&self) -> bool {
        self.buf.is_empty()
    }

    /// Get the size of the [Alloc].
    pub fn size(&self) -> Size {
        Size::from_bytes(self.len() as u64)
    }

    /// Get the alignment of the [Alloc].
    pub fn align(&self) -> Alignment {
        self.align
    }

    /// Get the mutability of the [Alloc].
    pub fn mutability(&self) -> Mutability {
        self.mutability
    }
}

static_single_store!(
    store = pub Allocations,
    id = pub AllocId,
    value = Alloc,
    store_name = allocations,
    store_source = ir_stores(),
    derives = Debug
);
