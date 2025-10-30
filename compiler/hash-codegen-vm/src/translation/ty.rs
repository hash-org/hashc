use hash_codegen::traits::ty::TypeBuilderMethods;

use crate::ctx::Ctx;

impl<'b> TypeBuilderMethods<'b> for Ctx<'b> {
    fn type_i1(&self) -> Self::Type {
        todo!()
    }

    fn type_i8(&self) -> Self::Type {
        todo!()
    }

    fn type_i16(&self) -> Self::Type {
        todo!()
    }

    fn type_i32(&self) -> Self::Type {
        todo!()
    }

    fn type_i64(&self) -> Self::Type {
        todo!()
    }

    fn type_i128(&self) -> Self::Type {
        todo!()
    }

    fn type_isize(&self) -> Self::Type {
        todo!()
    }

    fn type_ix(&self, _bits: u64) -> Self::Type {
        todo!()
    }

    fn type_f32(&self) -> Self::Type {
        todo!()
    }

    fn type_f64(&self) -> Self::Type {
        todo!()
    }

    fn type_array(&self, _ty: Self::Type, _len: u64) -> Self::Type {
        todo!()
    }

    fn type_function(&self, _args: &[Self::Type], _ret: Self::Type) -> Self::Type {
        todo!()
    }

    fn type_struct(&self, _els: &[Self::Type], _packed: bool) -> Self::Type {
        todo!()
    }

    fn type_ptr(&self) -> Self::Type {
        todo!()
    }

    fn type_ptr_ext(&self, _address_space: hash_codegen::target::abi::AddressSpace) -> Self::Type {
        todo!()
    }

    fn element_type(&self, _ty: Self::Type) -> Self::Type {
        todo!()
    }

    fn vector_length(&self, _ty: Self::Type) -> usize {
        todo!()
    }

    fn float_width(&self, _ty: Self::Type) -> usize {
        todo!()
    }

    fn int_width(&self, _ty: Self::Type) -> u64 {
        todo!()
    }

    fn ty_of_value(&self, _value: Self::Value) -> Self::Type {
        todo!()
    }

    fn ty_kind(&self, _ty: Self::Type) -> hash_codegen::common::TypeKind {
        todo!()
    }

    fn immediate_backend_ty(&self, _info: hash_codegen::repr::TyInfo) -> Self::Type {
        todo!()
    }

    fn scalar_pair_element_backend_ty(
        &self,
        _info: hash_codegen::repr::TyInfo,
        _index: usize,
        _immediate: bool,
    ) -> Self::Type {
        todo!()
    }

    fn backend_ty_from_info(&self, _info: hash_codegen::repr::TyInfo) -> Self::Type {
        todo!()
    }

    fn backend_ty_from_abi(&self, _abi: &hash_codegen::abi::FnAbi) -> Self::Type {
        todo!()
    }
}
