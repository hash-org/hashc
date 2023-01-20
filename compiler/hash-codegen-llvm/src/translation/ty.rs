//! Implements all of the type building methods for the LLVM
//! backend.

use hash_codegen::traits::ty::BuildTypeMethods;

use super::context::CodeGenCtx;

impl<'b> BuildTypeMethods<'b> for CodeGenCtx<'b> {
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

    fn type_f32(&self) -> Self::Type {
        todo!()
    }

    fn type_f64(&self) -> Self::Type {
        todo!()
    }

    fn type_array(&self, ty: Self::Type, len: u64) -> Self::Type {
        todo!()
    }

    fn type_function(&self, args: &[Self::Type], ret: Self::Type) -> Self::Type {
        todo!()
    }

    fn type_struct(&self, els: &[Self::Type], packed: bool) -> Self::Type {
        todo!()
    }

    fn type_ptr_to(&self, ty: Self::Type) -> Self::Type {
        todo!()
    }

    fn type_ptr_to_ext(
        &self,
        ty: Self::Type,
        address_space: hash_target::abi::AddressSpace,
    ) -> Self::Type {
        todo!()
    }

    fn element_type(&self, ty: Self::Type) -> Self::Type {
        todo!()
    }

    fn vector_length(&self, ty: Self::Type) -> usize {
        todo!()
    }

    fn float_width(&self, ty: Self::Type) -> usize {
        todo!()
    }

    fn int_width(&self, ty: Self::Type) -> u64 {
        todo!()
    }

    fn type_of_value(&self, value: Self::Value) -> Self::Type {
        todo!()
    }

    fn kind_of_type(&self, ty: Self::Type) -> hash_codegen::common::TypeKind {
        todo!()
    }

    fn immediate_backend_type(&self, info: hash_codegen::layout::TyInfo) -> Self::Type {
        todo!()
    }

    fn backend_type(&self, info: hash_codegen::layout::TyInfo) -> Self::Type {
        todo!()
    }

    fn backend_type_from_abi(&self, abi: &hash_codegen::abi::FnAbi) -> Self::Type {
        todo!()
    }
}
