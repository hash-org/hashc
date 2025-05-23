//! Contains utility data structures for managing type casts within the IR
//! and code generation stages. This module defines an auxiliary [CastTy]
//! to classify what kind of cast occurs between two types. Additionally,
//! this module provides the [CastKind] type which is used to classify
//! casts at the top level within RValue positions.

use hash_repr::ty::RefKind;
use hash_storage::store::statics::StoreId;

use crate::ty::{ReprTy, ReprTyId};

/// A [CastKind] represents all of the different kind of casts that
/// are permitted in the language. For now, this is just limited to
/// primitive types, i.e. from a float to an int, or from a char to
/// an i32, etc.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum CastKind {
    /// A cast from a float to an integral type.
    FloatToInt,

    /// A cast from a float to an integral type.
    IntToFloat,

    /// A cast from an integral type to another integral type.
    IntToInt,

    /// A float to float cast conversion, either converting from a `f32` into a
    /// `f64` or vice versa.
    FloatToFloat,

    /// A conversion between a reference (i.e. a pointer &T | &raw T) to
    /// an integral type.
    RefToInt,

    /// A conversion between a platform unsigned integer to a
    ///  reference (i.e. a pointer &T | &raw T).
    IntToRef,
}

impl CastKind {
    /// Classify the kind of cast between two types.
    pub fn classify(src: ReprTyId, dest: ReprTyId) -> Self {
        let src_ty = CastTy::from_ty(src);
        let dest_ty = CastTy::from_ty(dest);

        match (src_ty, dest_ty) {
            (Some(CastTy::Int(_)), Some(CastTy::Int(_))) => Self::IntToInt,
            (Some(CastTy::Int(_)), Some(CastTy::Float)) => Self::IntToFloat,
            (Some(CastTy::Float), Some(CastTy::Int(_))) => Self::FloatToInt,
            (Some(CastTy::Float), Some(CastTy::Float)) => Self::FloatToFloat,
            (Some(CastTy::Ref), Some(CastTy::Int(IntCastKind::UInt))) => Self::RefToInt,
            (Some(CastTy::Int(IntCastKind::UInt)), Some(CastTy::Ref)) => Self::IntToRef,
            _ => panic!(
                "attempting to cast between non-primitive types: src: `{}`, dest: `{}`",
                src, dest
            ),
        }
    }
}

/// Represents a classification of integer casts that can occur between
/// integral values within the IR. At code generation, most of these variants
/// are handled in the same way.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum IntCastKind {
    /// Converting into a unsigned integer type. Th   e size of the integer
    /// can be derived from the accompanying IR type.
    UInt,

    /// Converting into a signed integer type. The size of the integer
    /// can be derived from the accompanying IR type.
    Int,

    /// Converting into a `char` type.
    Char,

    /// Converting into a `bool` type.
    Bool,

    /// Converting a reference to `usize`.
    Ptr,
}

impl IntCastKind {
    /// Check whether the [IntCastKind] involves a signed integer.
    pub fn is_signed(self) -> bool {
        matches!(self, Self::Int)
    }
}

/// Represents a classification of type casts that can occur between
/// various types in the IR. This is a convince type to allow for
/// easy classification of casts between types when it comes to code
/// generation.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum CastTy {
    /// Integral type casts.
    Int(IntCastKind),

    /// Floating-point type casts.
    Float,

    /// Reference to a memory location.
    Ref,
}

impl CastTy {
    /// Convert a [ReprTy] into a [CastTy] if it is a primitive type. The
    /// function will return [`None`] if the conversion fails.
    pub fn from_ty(ty: ReprTyId) -> Option<Self> {
        ty.map(|ty| match ty {
            ReprTy::Int(_) => Some(Self::Int(IntCastKind::Int)),
            ReprTy::UInt(_) => Some(Self::Int(IntCastKind::UInt)),
            ReprTy::Char => Some(Self::Int(IntCastKind::Char)),
            ReprTy::Bool => Some(Self::Int(IntCastKind::Bool)),
            ReprTy::Float(_) => Some(Self::Float),
            ReprTy::Ref(_, _, RefKind::Raw | RefKind::Normal) => Some(Self::Ref),
            _ => None,
        })
    }
}
