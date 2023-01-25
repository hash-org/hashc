//! Implements all of the type building methods for the LLVM
//! backend.

use hash_codegen::{abi::FnAbi, common::TypeKind, layout::TyInfo, traits::ty::BuildTypeMethods};
use hash_ir::ty::IrTyId;
use hash_target::{abi::Scalar, size::Size};
use inkwell as llvm;

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

    fn ty_of_value(&self, value: Self::Value) -> Self::Type {
        todo!()
    }

    fn kind_of_ty(&self, ty: Self::Type) -> TypeKind {
        todo!()
    }

    fn immediate_backend_ty(&self, info: TyInfo) -> Self::Type {
        todo!()
    }

    fn backend_ty_from_ir_ty(&self, ty: IrTyId) -> Self::Type {
        todo!()
    }

    fn backend_ty_from_info(&self, info: TyInfo) -> Self::Type {
        todo!()
    }

    fn backend_ty_from_abi(&self, abi: &FnAbi) -> Self::Type {
        todo!()
    }
}

/// Define a trait that provides additional methods on the [CodeGenCtx]
/// for computing types as LLVM types, and various other related LLVM
/// specific type utilities.
pub trait ExtendedTyBuilderMethods<'ll> {
    /// Convert the [IrTyId] into the equivalent [llvm::types::AnyTypeEnum].
    fn llvm_ty(&self, ctx: &CodeGenCtx<'ll>) -> llvm::types::AnyTypeEnum<'ll>;

    /// Create an immediate type.
    fn immediate_llvm_ty(&self, ctx: &CodeGenCtx<'ll>) -> llvm::types::AnyTypeEnum<'ll>;

    /// Load the type of a [Scalar] with a specific offset.
    fn scalar_llvm_type_at(
        &self,
        ctx: &CodeGenCtx<'ll>,
        scalar: Scalar,
        offset: Size,
    ) -> llvm::types::AnyTypeEnum<'ll>;

    /// Create a type for a [`ScalarKind::Pair`].
    fn scalar_pair_element_llvm_ty(
        &self,
        ctx: &CodeGenCtx<'ll>,
        index: usize,
        immediate: bool,
    ) -> llvm::types::AnyTypeEnum<'ll>;
}

impl<'ll> ExtendedTyBuilderMethods<'ll> for TyInfo {
    fn llvm_ty(&self, ctx: &CodeGenCtx<'ll>) -> llvm::types::AnyTypeEnum<'ll> {
        todo!()
    }

    fn immediate_llvm_ty(&self, ctx: &CodeGenCtx<'ll>) -> llvm::types::AnyTypeEnum<'ll> {
        todo!()
    }

    fn scalar_llvm_type_at(
        &self,
        ctx: &CodeGenCtx<'ll>,
        scalar: Scalar,
        offset: Size,
    ) -> llvm::types::AnyTypeEnum<'ll> {
        todo!()
    }

    fn scalar_pair_element_llvm_ty(
        &self,
        ctx: &CodeGenCtx<'ll>,
        index: usize,
        immediate: bool,
    ) -> llvm::types::AnyTypeEnum<'ll> {
        todo!()
    }
}
