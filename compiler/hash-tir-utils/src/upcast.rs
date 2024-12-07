//! Logic and functionality to upcast REPR types into TIR types.
//!
//! @@Future: This is a fallible operation, it currently only supports
//! upcasting primitive types. This means that ADTs, functions, and other
//! more exotic types are not converted. This does not mean that they cannot
//! be converted into a [Ty]. REPR types are a subset of the possibilities
//! of [Ty] and hence should be convertable. The assumption is that there is
//! no requirement to convert more complex types at the mommment, but this is
//! certainly subject to change in the future.

use hash_repr::ty::{ReprTy, ReprTyId};
use hash_source::{FloatTy, SIntTy, UIntTy};
use hash_storage::store::statics::StoreId;
use hash_target::HasTarget;
use hash_tir::{
    intrinsics::definitions::*,
    tir::{DataDefId, NodeOrigin, Ty, TyId},
};
use hash_utils::derive_more::{Constructor, Deref};

#[derive(Constructor, Deref)]
pub struct TyUpCast<'tc, E> {
    #[deref]
    env: &'tc E,
}

impl<E: HasTarget> TyUpCast<'_, E> {
    /// Convert a [ReprTyId] into a [TyId].
    pub fn ty_from_repr_ty(&self, ty: ReprTyId, origin: impl Into<NodeOrigin>) -> Option<TyId> {
        match ty.value() {
            ReprTy::Int(_)
            | ReprTy::UInt(_)
            | ReprTy::Float(_)
            | ReprTy::Str
            | ReprTy::Bool
            | ReprTy::Char
            | ReprTy::Never => Some(Ty::data_ty(self.data_def_from_repr_ty(ty)?, origin.into())),
            _ => None,
        }
    }

    /// Get the relevant [DataDefId] for a [ReprTyId].
    ///
    /// ##Note: This currently onlyu suports primitive types.
    ///
    /// @@Improvement: do we need caching when it comes to more complex types?
    /// @@Improvement: should we provide locations to these types?
    pub fn data_def_from_repr_ty(&self, ty: ReprTyId) -> Option<DataDefId> {
        match ty.value() {
            ReprTy::Int(ty) => match ty {
                SIntTy::I8 => Some(i8_def()),
                SIntTy::I16 => Some(i16_def()),
                SIntTy::I32 => Some(i32_def()),
                SIntTy::I64 => Some(i64_def()),
                SIntTy::I128 => Some(i128_def()),
                SIntTy::ISize => Some(isize_def()),
            },
            ReprTy::UInt(ty) => match ty {
                UIntTy::U8 => Some(u8_def()),
                UIntTy::U16 => Some(u16_def()),
                UIntTy::U32 => Some(u32_def()),
                UIntTy::U64 => Some(u64_def()),
                UIntTy::U128 => Some(u128_def()),
                UIntTy::USize => Some(usize_def()),
            },
            ReprTy::Float(ty) => match ty {
                FloatTy::F32 => Some(f32_def()),
                FloatTy::F64 => Some(f64_def()),
            },
            ReprTy::Bool => Some(bool_def()),
            ReprTy::Char => Some(char_def()),
            ReprTy::Never => Some(never_def()),
            ReprTy::Ref(ty, _, _) => {
                if ty.map(|inner| matches!(inner, ReprTy::Str)) {
                    Some(str_def())
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}
