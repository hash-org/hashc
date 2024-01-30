//! Hash source interned constant store. This is a data store
//! for interning observed constants within the source file of
//! a program. This is done so that constants don't need to
//! be passed around each stage of the compiler and can just
//! be interned, and accessed when needed.

use std::fmt::Debug;

use hash_source::constant::{AllocId, Scalar};
use hash_storage::store::statics::StoreId;
use hash_target::data_layout::HasDataLayout;
// Re-export the "primitives" from the hash-target crate so that everyone can use
// them who depends on `hash-source`
pub use hash_target::primitives::*;
pub use hash_target::size::Size;
use hash_utils::{derive_more::Constructor, num_bigint::BigInt};
use paste::paste;

use crate::ty::{ReprTyId, COMMON_REPR_TYS};

pub trait Ty: Sized + Clone + Copy + PartialEq + Eq + Into<IntTy> + Into<ReprTyId> + Debug {
    // const ZERO: Self;
    // const BOOL: Self;
    // const CHAR: Self;
    // const STR: Self;

    // const I8: Self;
    // const I16: Self;
    // const I32: Self;
    // const I64: Self;
    // const I128: Self;
    // const ISIZE: Self;

    // const U8: Self;
    // const U16: Self;
    // const U32: Self;
    // const U64: Self;
    // const U128: Self;
    // const USIZE: Self;

    // const F32: Self;
    // const F64: Self;

    // // @@Future: when we figure out how to make layout stuff
    // // more agnostic, we can `layout_of` and `ty_info` here.
    // // fn layout_of(&self) -> LayoutId;
    // //
    // // fn ty_info(&self) -> TyInfo<Ty> {
    // //  TyInfo { ty: *self, layout: self.layout_of() }
    // // }

    // fn is_switchable(&self) -> bool;

    // fn is_signed(&self) -> bool;
}

impl Ty for ReprTyId {}

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
    ty: ReprTyId,

    /// The kind of constant that is stored.
    pub kind: ConstKind,
}

impl Const {
    /// Create a ZST constant.
    pub fn zero() -> Self {
        Self::new(COMMON_REPR_TYS.unit, ConstKind::Zero)
    }

    /// Create a ZST constant which is of `zero` size with
    /// a type.
    pub fn zst(ty: ReprTyId) -> Self {
        Self::new(ty, ConstKind::Zero)
    }

    /// Create a new allocated constant, from a given type and allocation,
    /// assuming that the offset of the allocation is zero.
    pub fn alloc(alloc: AllocId, ty: ReprTyId) -> Self {
        Self::new(ty, ConstKind::Alloc { alloc, offset: Size::ZERO })
    }

    /// Create a new allocated string constant, from a given [AllocId].
    pub fn str(alloc: AllocId) -> Self {
        Self::new(COMMON_REPR_TYS.str, ConstKind::Alloc { alloc, offset: Size::ZERO })
    }

    /// Create a new scalar [Const] from a given type and [Scalar] value.
    pub fn scalar(scalar: Scalar, ty: ReprTyId) -> Self {
        Self::new(ty, ConstKind::Scalar(scalar))
    }

    /// Check if the [Const] is a zero value.
    pub fn is_zero(&self) -> bool {
        matches!(self.kind, ConstKind::Zero)
    }

    /// Get the type of the constant.
    pub fn ty(&self) -> ReprTyId {
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
    pub fn as_alloc(&self) -> AllocId {
        match self.kind {
            ConstKind::Alloc { alloc, .. } => alloc,
            _ => panic!("Const is not an allocation"),
        }
    }

    /// Assume that the current [Const] is a [Scalar] value and return it.
    pub fn as_scalar(&self) -> Scalar {
        match self.kind {
            ConstKind::Scalar(scalar) => scalar,
            _ => panic!("Const is not a scalar"),
        }
    }

    /// Create a new [Const] from a integer with the given type.
    pub fn from_scalar_like<C: HasDataLayout>(value: u128, ty: ReprTyId, ctx: &C) -> Self {
        let kind = if ty == COMMON_REPR_TYS.bool {
            // @@FixMe: we're converting from one to another... seems dumb!
            ConstKind::Scalar(Scalar::from_bool(value != 0))
        } else {
            let size = Into::<IntTy>::into(ty.value()).size(ctx.data_layout().pointer_size);
            ConstKind::Scalar(Scalar::from_uint(value, size))
        };

        Const { ty, kind }
    }

    /// Create a boolean constant.
    pub fn bool(value: bool) -> Self {
        Self::new(COMMON_REPR_TYS.bool, ConstKind::Scalar(Scalar::from_bool(value)))
    }

    /// Create a character constant.
    pub fn char(value: char) -> Self {
        Self::new(COMMON_REPR_TYS.char, ConstKind::Scalar(Scalar::from(value)))
    }

    /// Create a new [Const] which represents a `usize`.
    pub fn usize<C: HasDataLayout>(value: u64, ctx: &C) -> Self {
        let kind = ConstKind::Scalar(Scalar::from_usize(value, ctx));
        Self::new(COMMON_REPR_TYS.usize, kind)
    }

    /// Attempt to coerce a [Const] into a `usize`.
    pub fn try_to_target_usize<C: HasDataLayout>(&self, ctx: &C) -> Option<usize> {
        if self.ty == COMMON_REPR_TYS.usize {
            self.as_scalar().to_target_usize(ctx).try_into().ok()
        } else {
            None
        }
    }

    pub fn as_big_int(&self) -> BigInt {
        match self.kind {
            ConstKind::Scalar(scalar) => scalar.to_big_int(self.ty.is_signed()),
            ConstKind::Alloc { alloc, .. } => alloc.to_big_int(self.ty.is_signed()),
            _ => panic!("cannot cast to bigint"),
        }
    }
}

macro_rules! const_from_ty_impl {
    ($($ty:ident),*) => {
        $(
            impl From<$ty> for Const {
                fn from(value: $ty) -> Self {
                    Const::new(paste!(COMMON_REPR_TYS.[<$ty>]), ConstKind::Scalar(Scalar::from(value)))
                }
            }
        )*
    };
}

const_from_ty_impl!(f32, f64, char, u8, u16, u32, u64, u128);

macro_rules! try_from {
    ($($ty:ty),*) => {
        $(
            impl TryFrom<&Const> for $ty {
                type Error = Size;
                #[inline]
                fn try_from(value: &Const) -> Result<Self, Size> {
                    // The `unwrap` cannot fail because to_bits (if it succeeds)
                    // is guaranteed to return a value that fits into the size.
                    let ConstKind::Scalar(scalar) = value.kind else {
                        return Err(Size::ZERO) // @@Todo: change this to be more specific to the error?
                    };

                    scalar.to_bits(Size::from_bytes(std::mem::size_of::<$ty>()))
                       .map(|u| u.try_into().unwrap())
                }
            }
        )*
    }
}

try_from!(u8, u16, u32, u64, u128);

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
        data: AllocId,

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

// impl ConstKind {
//     /// Create a [ConstKind] from a TIR literal.
//     pub fn from_lit<C: HasDataLayout>(lit: Lit, ctx: &C) -> Self {
//         match lit {
//             Lit::Int(int) => ConstKind::Scalar(Scalar::from(int.value())),
//             Lit::Float(float) =>
// ConstKind::Scalar(Scalar::from(float.value())),             Lit::Str(str) =>
// {                 let data = str.interned_value();
//                 ConstKind::Pair { data, len: Scalar::from_usize(data.len() as
// u64, ctx) }             }
//             Lit::Char(ch) => ConstKind::Scalar(Scalar::from(ch.value())),
//         }
//     }
// }
