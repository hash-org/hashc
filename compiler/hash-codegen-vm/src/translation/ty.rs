use hash_codegen::{
    abi, common,
    repr::TyInfo,
    target::{HasTarget, abi::AddressSpace},
    traits::{BackendTypes, layout::LayoutMethods, ty::TypeBuilderMethods},
};
use hash_ir::ty::{COMMON_REPR_TYS, FnTy, ReprTy, ReprTyListId};
use hash_source::FloatTy;
use hash_storage::store::statics::{SingleStoreValue, StoreId};

use crate::ctx::Ctx;

impl<'b> TypeBuilderMethods<'b> for Ctx<'b> {
    fn type_i1(&self) -> Self::Type {
        COMMON_REPR_TYS.bool
    }

    fn type_i8(&self) -> Self::Type {
        COMMON_REPR_TYS.i8
    }

    fn type_i16(&self) -> Self::Type {
        COMMON_REPR_TYS.i16
    }

    fn type_i32(&self) -> Self::Type {
        COMMON_REPR_TYS.i32
    }

    fn type_i64(&self) -> Self::Type {
        COMMON_REPR_TYS.i64
    }

    fn type_i128(&self) -> Self::Type {
        COMMON_REPR_TYS.i128
    }

    fn type_isize(&self) -> Self::Type {
        COMMON_REPR_TYS.isize
    }

    fn type_ix(&self, bits: u64) -> Self::Type {
        match bits {
            8 => COMMON_REPR_TYS.i8,
            16 => COMMON_REPR_TYS.i16,
            32 => COMMON_REPR_TYS.i32,
            64 => COMMON_REPR_TYS.i64,
            128 => COMMON_REPR_TYS.i128,
            // @@BigInts: support big integers?
            _ => panic!("unsupported integer width: {bits}"),
        }
    }

    fn type_f32(&self) -> Self::Type {
        COMMON_REPR_TYS.f32
    }

    fn type_f64(&self) -> Self::Type {
        COMMON_REPR_TYS.f64
    }

    fn type_array(&self, ty: Self::Type, length: u64) -> Self::Type {
        ReprTy::create(ReprTy::Array { ty, length: length as usize })
    }

    fn type_function(&self, args: &[Self::Type], ret: Self::Type) -> Self::Type {
        ReprTy::create(ReprTy::Fn(FnTy {
            params: ReprTyListId::seq(args.iter().copied()),
            return_ty: ret,
        }))
    }

    fn type_struct(&self, els: &[Self::Type], _packed: bool) -> Self::Type {
        // we don't need to do anything for `_packed` in the VM.
        ReprTy::create(ReprTy::tuple(els))
    }

    fn type_ptr(&self) -> Self::Type {
        COMMON_REPR_TYS.ptr
    }

    fn type_ptr_ext(&self, _address_space: AddressSpace) -> Self::Type {
        COMMON_REPR_TYS.ptr
    }

    fn element_type(&self, ty: Self::Type) -> Self::Type {
        ty.borrow().element_ty().unwrap()
    }

    fn vector_length(&self, ty: Self::Type) -> usize {
        // Although: array types like [X; N] are supported which are effectively
        // vectors?
        unimplemented!("vector types are not supported yet: {ty:#?}")
    }

    fn float_width(&self, ty: Self::Type) -> usize {
        ty.borrow().as_float().size().bits() as usize
    }

    fn int_width(&self, ty: Self::Type) -> u64 {
        ty.borrow().as_int().size(self.target().ptr_size()).bits()
    }

    fn ty_of_value(&self, value: Self::Value) -> Self::Type {
        value.ty()
    }

    /// This method maps a backend type to a [TypeKind].
    ///
    /// I don't think this is really needed by the VM backend, but we implement
    /// it anyway for completeness.
    fn ty_kind(&self, ty: Self::Type) -> common::TypeKind {
        let info = self.layout_of(ty);

        // 1. Check that if this is a ZST, this is basically a `void` type.
        if info.is_zst() {
            return common::TypeKind::Void;
        }

        // The rest are a trivial mapping from ReprTy to TypeKind.
        ty.map(|ty| match ty {
            ReprTy::Bool | ReprTy::Char | ReprTy::UInt(..) | ReprTy::Int(..) => {
                common::TypeKind::Integer
            }
            ReprTy::Float(FloatTy::F32) => common::TypeKind::Float,
            ReprTy::Float(FloatTy::F64) => common::TypeKind::Double,
            ReprTy::Ref { .. } => common::TypeKind::Pointer,
            ReprTy::Array { .. } => common::TypeKind::Array,
            ReprTy::FnDef { .. } | ReprTy::Fn { .. } => common::TypeKind::Function,
            ReprTy::Slice(..) | ReprTy::Str | ReprTy::Adt { .. } => common::TypeKind::Struct,
            ReprTy::Never => common::TypeKind::Void,
        })
    }

    fn immediate_backend_ty(&self, info: TyInfo) -> Self::Type {
        info.ty
    }

    fn scalar_pair_element_backend_ty(
        &self,
        info: TyInfo,
        index: usize,
        immediate: bool,
    ) -> Self::Type {
        info.scalar_pair_element_ty(index, immediate)
    }

    fn backend_ty_from_info(&self, info: TyInfo) -> Self::Type {
        info.ty
    }

    fn backend_ty_from_abi(&self, abi: &abi::FnAbi) -> Self::Type {
        abi.ty
    }
}

trait ExtendedTyBuilderMethods<'m> {
    fn scalar_pair_element_ty(
        &self,
        index: usize,
        immediate: bool,
    ) -> <Ctx<'m> as BackendTypes>::Type;
}

impl<'m> ExtendedTyBuilderMethods<'m> for TyInfo {
    fn scalar_pair_element_ty(&self, index: usize, _: bool) -> <Ctx<'m> as BackendTypes>::Type {
        self.ty.map(|ty| {
            let adt = ty.as_adt().borrow();
            let variant = adt.univariant();

            variant.fields[index].ty
        })
    }
}
