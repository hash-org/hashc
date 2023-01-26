//! Implements all of the type building methods for the LLVM
//! backend.

use core::panic;

use hash_codegen::{abi::FnAbi, common::TypeKind, layout::TyInfo, traits::ty::BuildTypeMethods};
use hash_ir::ty::IrTyId;
use hash_target::{
    abi::{AddressSpace, Scalar},
    size::Size,
};
use inkwell as llvm;
use llvm::types::{AnyTypeEnum, AsTypeRef, BasicType, BasicTypeEnum};
use llvm_sys::{core::LLVMGetTypeKind, LLVMTypeKind};

use super::{abi::ExtendedFnAbiMethods, context::CodeGenCtx, AddressSpaceWrapper};

/// Convert a [BasicTypeEnum] into a [AnyTypeEnum].
///
/// @@PatchInkwell: maybe patch inkwell in order to support this conversion just
/// using a `From` trait.
pub fn convert_basic_ty_to_any<'b>(ty: BasicTypeEnum<'b>) -> AnyTypeEnum<'b> {
    match ty {
        BasicTypeEnum::ArrayType(ty) => AnyTypeEnum::ArrayType(ty),
        BasicTypeEnum::FloatType(ty) => AnyTypeEnum::FloatType(ty),
        BasicTypeEnum::IntType(ty) => AnyTypeEnum::IntType(ty),
        BasicTypeEnum::PointerType(ty) => AnyTypeEnum::PointerType(ty),
        BasicTypeEnum::StructType(ty) => AnyTypeEnum::StructType(ty),
        BasicTypeEnum::VectorType(ty) => AnyTypeEnum::VectorType(ty),
    }
}

impl<'b> BuildTypeMethods<'b> for CodeGenCtx<'b> {
    fn type_i1(&self) -> Self::Type {
        self.ll_ctx.bool_type().into()
    }

    fn type_i8(&self) -> Self::Type {
        self.ll_ctx.i8_type().into()
    }

    fn type_i16(&self) -> Self::Type {
        self.ll_ctx.i16_type().into()
    }

    fn type_i32(&self) -> Self::Type {
        self.ll_ctx.i32_type().into()
    }

    fn type_i64(&self) -> Self::Type {
        self.ll_ctx.i64_type().into()
    }

    fn type_i128(&self) -> Self::Type {
        self.ll_ctx.i128_type().into()
    }

    fn type_isize(&self) -> Self::Type {
        self.ll_ctx.i64_type().into()
    }

    fn type_f32(&self) -> Self::Type {
        self.ll_ctx.f32_type().into()
    }

    fn type_f64(&self) -> Self::Type {
        self.ll_ctx.f64_type().into()
    }

    fn type_array(&self, ty: Self::Type, len: u64) -> Self::Type {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        ty.array_type(len as u32).into()
    }

    fn type_function(&self, args: &[Self::Type], ret: Self::Type) -> Self::Type {
        let ret: BasicTypeEnum = ret.try_into().unwrap();
        let args = args.iter().map(|ty| (*ty).try_into().unwrap()).collect::<Vec<_>>();
        ret.fn_type(&args, false).into()
    }

    fn type_struct(&self, fields: &[Self::Type], packed: bool) -> Self::Type {
        let fields = fields.iter().map(|ty| (*ty).try_into().unwrap()).collect::<Vec<_>>();
        self.ll_ctx.struct_type(&fields, packed).into()
    }

    fn type_ptr_to(&self, ty: Self::Type) -> Self::Type {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        let AddressSpaceWrapper(addr) = AddressSpace::DATA.into();
        ty.ptr_type(addr).into()
    }

    fn type_ptr_to_ext(&self, ty: Self::Type, address_space: AddressSpace) -> Self::Type {
        let ty: BasicTypeEnum = ty.try_into().unwrap();
        let AddressSpaceWrapper(addr) = address_space.into();
        ty.ptr_type(addr).into()
    }

    fn element_type(&self, ty: Self::Type) -> Self::Type {
        match ty {
            llvm::types::AnyTypeEnum::ArrayType(array) => {
                convert_basic_ty_to_any(array.get_element_type())
            }
            llvm::types::AnyTypeEnum::VectorType(vec) => {
                convert_basic_ty_to_any(vec.get_element_type())
            }
            llvm::types::AnyTypeEnum::PointerType(_) => {
                panic!("`element_type` not supported on opaque pointer type")
            }
            _ => panic!("`element_type` called on element-like type"),
        }
    }

    fn vector_length(&self, ty: Self::Type) -> usize {
        let AnyTypeEnum::VectorType(vec) = ty else {
            panic!("`vector_length` called on non-vector type")
        };

        vec.get_size() as usize
    }

    fn float_width(&self, ty: Self::Type) -> usize {
        let kind = self.ty_kind(ty);

        match kind {
            TypeKind::Float => 32,
            TypeKind::Double => 64,
            TypeKind::X86FP80 => 80,
            TypeKind::FP128 | TypeKind::PPCFP128 => 128,
            _ => panic!("`float_width` called on non-float type"),
        }
    }

    fn int_width(&self, ty: Self::Type) -> u64 {
        ty.into_int_type().get_bit_width() as u64
    }

    fn ty_of_value(&self, value: Self::Value) -> Self::Type {
        value.get_type()
    }

    /// Compute the [TypeKind] from the given [AnyTypeEnum] using
    /// [`LLVMGetTypeKind`].
    fn ty_kind(&self, ty: Self::Type) -> TypeKind {
        let kind = unsafe { LLVMGetTypeKind(ty.as_type_ref()) };

        match kind {
            LLVMTypeKind::LLVMVoidTypeKind => TypeKind::Void,
            LLVMTypeKind::LLVMHalfTypeKind => TypeKind::Half,
            LLVMTypeKind::LLVMFloatTypeKind => TypeKind::Float,
            LLVMTypeKind::LLVMDoubleTypeKind => TypeKind::Double,
            LLVMTypeKind::LLVMX86_FP80TypeKind => TypeKind::X86FP80,
            LLVMTypeKind::LLVMFP128TypeKind => TypeKind::FP128,
            LLVMTypeKind::LLVMPPC_FP128TypeKind => TypeKind::PPCFP128,
            LLVMTypeKind::LLVMLabelTypeKind => TypeKind::Label,
            LLVMTypeKind::LLVMIntegerTypeKind => TypeKind::Integer,
            LLVMTypeKind::LLVMFunctionTypeKind => TypeKind::Function,
            LLVMTypeKind::LLVMStructTypeKind => TypeKind::Struct,
            LLVMTypeKind::LLVMArrayTypeKind => TypeKind::Array,
            LLVMTypeKind::LLVMPointerTypeKind => TypeKind::Pointer,
            LLVMTypeKind::LLVMVectorTypeKind => TypeKind::FixedVector,
            LLVMTypeKind::LLVMMetadataTypeKind => TypeKind::Metadata,
            LLVMTypeKind::LLVMX86_MMXTypeKind => TypeKind::X86MMX,
            LLVMTypeKind::LLVMTokenTypeKind => TypeKind::Token,
            LLVMTypeKind::LLVMScalableVectorTypeKind => TypeKind::ScalableVector,
            LLVMTypeKind::LLVMBFloatTypeKind => TypeKind::Float,
            LLVMTypeKind::LLVMX86_AMXTypeKind => TypeKind::X86AMX,
        }
    }

    fn immediate_backend_ty(&self, info: TyInfo) -> Self::Type {
        info.immediate_llvm_ty(self)
    }

    fn backend_ty_from_info(&self, info: TyInfo) -> Self::Type {
        info.llvm_ty(self)
    }

    fn backend_ty_from_abi(&self, abi: &FnAbi) -> Self::Type {
        abi.llvm_ty(self)
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
