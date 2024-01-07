//! Hash source interned constant store. This is a data store
//! for interning observed constants within the source file of
//! a program. This is done so that constants don't need to
//! be passed around each stage of the compiler and can just
//! be interned, and accessed when needed.

use std::{
    borrow::Cow,
    collections::HashMap,
    fmt,
    io::{self, Read},
    num::NonZeroU8,
    ops::{Deref, DerefMut},
    sync::OnceLock,
};

use hash_storage::{static_single_store, stores};
// Re-export the "primitives" from the hash-target crate so that everyone can use
// them who depends on `hash-source`
pub use hash_target::primitives::*;
pub use hash_target::size::Size;
use hash_target::{
    alignment::Alignment,
    data_layout::{Endian, HasDataLayout},
};
use hash_utils::{derive_more::Constructor, fnv::FnvBuildHasher};
use num_bigint::BigInt;

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

macro_rules! scalar_impl_from_uint_ty {
    ($($ty:ty),*) => {
        $(
            impl From<$ty> for Scalar {
                #[inline]
                fn from(u: $ty) -> Self {
                    Self {
                        value: u128::from(u),
                        size: NonZeroU8::new(std::mem::size_of::<$ty>() as u8).unwrap(),
                    }
                }
            }
        )*
    }
}

scalar_impl_from_uint_ty!(u8, u16, u32, u64, u128, bool);

macro_rules! scalar_impl_from_sint_ty {
    ($($ty:ty),*) => {
        $(
            impl From<$ty> for Scalar {
                #[inline]
                fn from(u: $ty) -> Self {
                    let value = i128::from(u);
                    let size = NonZeroU8::new(std::mem::size_of::<$ty>() as u8).unwrap();
                    let truncated = Size::from_bytes(size.get()).truncate(value as u128);

                    Self {
                        value: truncated,
                        size,
                    }
                }
            }
        )*
    }
}

scalar_impl_from_sint_ty!(i8, i16, i32, i64, i128);
// impl From<IntConstant> for Scalar {
//     fn from(value: IntConstant) -> Self {
//         let size = value.size();

//         match value.value {
//             IntConstantValue::I8(val) => Scalar::from_int(val, size),
//             IntConstantValue::I16(val) => Scalar::from_int(val, size),
//             IntConstantValue::I32(val) => Scalar::from_int(val, size),
//             IntConstantValue::I64(val) => Scalar::from_int(val, size),
//             IntConstantValue::I128(val) => Scalar::from_int(val, size),
//             IntConstantValue::U8(val) => Scalar::from_uint(val, size),
//             IntConstantValue::U16(val) => Scalar::from_uint(val, size),
//             IntConstantValue::U32(val) => Scalar::from_uint(val, size),
//             IntConstantValue::U64(val) => Scalar::from_uint(val, size),
//             IntConstantValue::U128(val) => Scalar::from_uint(val, size),
//         }
//     }
// }

/// Read a unsigned integer from the given source buffer. This supports buffers
/// of up to 16 bytes in length, and will automatically convert it into a
/// `u128`.
///
/// If the desired size should be smaller than a `u128` (which) is often the
/// case, the integer can be "truncated" using [`Size::truncate`].
pub fn read_target_uint(endian: Endian, mut data: &[u8]) -> io::Result<u128> {
    // This u128 holds an "any-size uint" (since smaller uints can fits in it)
    let mut buf = [0u8; std::mem::size_of::<u128>()];

    // So we do not read exactly 16 bytes into the u128, just the "payload".
    let uint = match endian {
        Endian::Little => {
            let _ = data.read(&mut buf)?;
            u128::from_le_bytes(buf)
        }
        Endian::Big => {
            let _ = data.read(&mut buf[16 - data.len()..])?;
            u128::from_be_bytes(buf)
        }
    };

    debug_assert!(data.is_empty()); // We should have consumed the source buffer.
    Ok(uint)
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

#[derive(Clone, Copy, Debug)]
pub enum Mutability {
    Mutable,
    Immutable,
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
    store_source = const_stores(),
    derives = Debug
);

impl AllocId {
    /// Attempt to convert a particular [AllocId] into a [String] value.
    ///
    /// This method will just take the raw allocated bytes and "treat" them
    /// as a standard utf8 string.
    ///
    ///##NOTE: If the bytes are not valid utf8 then this  method will panic.
    pub fn coerce_into_str(&self) -> String {
        todo!()
    }

    pub fn string(_value: String) -> Self {
        todo!()
    }

    pub fn big_int(_value: BigInt) -> Self {
        todo!()
    }
}

/// A [LocalStringTable] can be used by a thread to intern strings, and later
/// push them into the global [StringTable].
#[derive(Default)]
pub struct LocalStringTable {
    /// The table itself.
    table: HashMap<String, AllocId, FnvBuildHasher>,

    /// The largest key that was inserted into the table. This is used to know
    /// exactly how much to reserve in the global string table.
    max_key: Option<AllocId>,
}

impl LocalStringTable {
    /// Add an entry to the local string table.
    #[inline]
    pub fn add(&mut self, value: String) -> AllocId {
        let key = *self.table.entry(value.clone()).or_insert_with(|| AllocId::string(value));
        self.max_key = std::cmp::max(self.max_key, Some(key));
        key
    }
}

stores!(
    ConstStores;
    allocations: Allocations
);

impl ConstStores {
    /// Add a collection of interned strings from a given map.
    pub fn add_local_table(&self, _local: LocalStringTable) {
        // if local.table.is_empty() {
        //     return;
        // }

        // // Acquire the writer and merge the table into the main one.
        // let mut writer = self.table.write();
        // let index = local.max_key.unwrap().to_usize();
        // StringTable::reserve(&mut writer, index);

        // for (key, value) in local.table {
        //     writer[value.to_usize()] = Some(Box::leak(key.into_boxed_str()));
        // }
        todo!()
    }
}

/// The global [`ConstStores`] instance.
static STORES: OnceLock<ConstStores> = OnceLock::new();

/// Access the global [`ConstStores`] instance.
pub fn const_stores() -> &'static ConstStores {
    STORES.get_or_init(ConstStores::new)
}
