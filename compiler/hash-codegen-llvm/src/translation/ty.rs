//! Implements all of the type building methods for the LLVM
//! backend.

use core::panic;

use hash_codegen::{
    abi::FnAbi,
    common::TypeKind,
    repr::{Layout, LayoutShape, TyInfo, Variants},
    target::{
        abi::{AbiRepresentation, AddressSpace, Integer, Scalar, ScalarKind},
        alignment::Alignment,
        size::Size,
    },
    traits::{HasCtxMethods, ty::TypeBuilderMethods},
};
use hash_ir::ty::ReprTy;
use hash_storage::store::statics::StoreId;
use hash_utils::smallvec::{SmallVec, smallvec};
use inkwell as llvm;
use llvm::{
    context::AsContextRef,
    types::{AnyType, AnyTypeEnum, AsTypeRef, BasicType, BasicTypeEnum, MetadataType, VectorType},
};
use llvm_sys::{
    LLVMTypeKind,
    core::{LLVMGetTypeKind, LLVMPointerTypeInContext, LLVMVectorType},
};

use super::abi::ExtendedFnAbiMethods;
use crate::ctx::CodeGenCtx;

/// Convert a [BasicTypeEnum] into a [AnyTypeEnum].
///
/// @@PatchInkwell: maybe patch inkwell in order to support this conversion just
/// using a `From` trait.
pub fn convert_basic_ty_to_any(ty: BasicTypeEnum) -> AnyTypeEnum {
    match ty {
        BasicTypeEnum::ArrayType(ty) => AnyTypeEnum::ArrayType(ty),
        BasicTypeEnum::FloatType(ty) => AnyTypeEnum::FloatType(ty),
        BasicTypeEnum::IntType(ty) => AnyTypeEnum::IntType(ty),
        BasicTypeEnum::PointerType(ty) => AnyTypeEnum::PointerType(ty),
        BasicTypeEnum::StructType(ty) => AnyTypeEnum::StructType(ty),
        BasicTypeEnum::VectorType(ty) => AnyTypeEnum::VectorType(ty),
        BasicTypeEnum::ScalableVectorType(ty) => AnyTypeEnum::ScalableVectorType(ty),
    }
}

impl<'m> CodeGenCtx<'_, 'm> {
    /// Create a [VectorType] from a [`AbiRepresentation::Vector`].
    pub(crate) fn type_vector(&self, element_ty: AnyTypeEnum<'m>, len: u64) -> AnyTypeEnum<'m> {
        // @@PatchInkwell: we should allow creating a vector type from a
        // BasicTypeEnum and a length.
        let vec_ty = unsafe {
            let ty = LLVMVectorType(element_ty.as_type_ref(), len as u32);
            VectorType::new(ty)
        };

        AnyTypeEnum::VectorType(vec_ty)
    }

    /// Create a `void` type, which is used for functions that don't return
    /// any value, equivalently a `()` type.
    pub(crate) fn type_void(&self) -> AnyTypeEnum<'m> {
        self.ll_ctx.void_type().into()
    }

    /// Create a metadata type tht might be used to interact with some
    /// LLVM intrinsics and debug information.
    pub(crate) fn type_metadata(&self) -> MetadataType<'m> {
        self.ll_ctx.metadata_type()
    }

    /// Create a type that represents the padding that is needed for a
    /// particular [Size] and [Alignment].
    pub(crate) fn type_padding(&self, size: Size, alignment: Alignment) -> AnyTypeEnum<'m> {
        let unit = Integer::approximate_alignment(self, alignment);

        let size = size.bytes();
        let unit_size = unit.size().bytes();
        debug_assert_eq!(size % unit_size, 0);
        self.type_array(self.type_from_integer(unit), size / unit_size)
    }
}

impl<'b> TypeBuilderMethods<'b> for CodeGenCtx<'b, '_> {
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

    fn type_ix(&self, bits: u64) -> Self::Type {
        self.ll_ctx.custom_width_int_type(bits.try_into().unwrap()).as_any_type_enum()
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
        let args = args.iter().map(|ty| (*ty).try_into().unwrap()).collect::<Vec<_>>();

        // @@Inkwell: somehow `void` types aren't in the `BasicTypeEnum` enum??
        if let AnyTypeEnum::VoidType(_) = ret {
            ret.into_void_type().fn_type(&args, false).into()
        } else {
            let ret: BasicTypeEnum = ret.try_into().unwrap();
            ret.fn_type(&args, false).into()
        }
    }

    fn type_struct(&self, fields: &[Self::Type], packed: bool) -> Self::Type {
        let fields = fields.iter().map(|ty| (*ty).try_into().unwrap()).collect::<Vec<_>>();
        self.ll_ctx.struct_type(&fields, packed).into()
    }

    fn type_ptr(&self) -> Self::Type {
        self.type_ptr_ext(AddressSpace::DATA)
    }

    fn type_ptr_ext(&self, address_space: AddressSpace) -> Self::Type {
        // @@PatchInkwell: allow for opaque pointers to be created.
        unsafe {
            AnyTypeEnum::new(LLVMPointerTypeInContext(self.ll_ctx.as_ctx_ref(), address_space.0))
        }
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
            LLVMTypeKind::LLVMTargetExtTypeKind => TypeKind::TargetExtensionTy,
        }
    }

    fn immediate_backend_ty(&self, info: TyInfo) -> Self::Type {
        info.immediate_llvm_ty(self)
    }

    fn scalar_pair_element_backend_ty(
        &self,
        info: TyInfo,
        index: usize,
        immediate: bool,
    ) -> Self::Type {
        info.scalar_pair_element_llvm_ty(self, index, immediate)
    }

    fn backend_ty_from_info(&self, info: TyInfo) -> Self::Type {
        info.llvm_ty(self)
    }

    fn backend_ty_from_abi(&self, abi: &FnAbi) -> Self::Type {
        abi.llvm_ty(self)
    }
}

/// A [TyMemoryRemap] is a type that is used to represent the occurred
/// memory field re-mapping that occurs when lowering a type to LLVM.
/// This re-mapping originates from the fact that "padding" within types
/// now becomes a concrete type, and thus the memory layout of the type
/// changes if padding slots are inserted. If the type had any re-maps,
/// then the [TyMemoryRemap] will contain a `remap` field with the
/// new memory to source field mapping.
pub(crate) struct TyMemoryRemap<'m> {
    /// The lowered type.
    pub ty: AnyTypeEnum<'m>,

    /// If the type was re-mapped, this is a reference
    /// to the new memory map which should be used over the
    /// one that is stored in the [LayoutShape] of a [Layout].
    pub remap: Option<SmallVec<[u32; 4]>>,
}

/// Define a trait that provides additional methods on the [CodeGenCtx]
/// for computing types as LLVM types, and various other related LLVM
/// specific type utilities.
pub(crate) trait ExtendedTyBuilderMethods<'m> {
    /// Convert the [ReprTyId] into the equivalent [llvm::types::AnyTypeEnum].
    fn llvm_ty(&self, ctx: &CodeGenCtx<'_, 'm>) -> llvm::types::AnyTypeEnum<'m>;

    /// Create an immediate type.
    fn immediate_llvm_ty(&self, ctx: &CodeGenCtx<'_, 'm>) -> llvm::types::AnyTypeEnum<'m>;

    /// Load the type of a [Scalar] with a specific offset.
    fn scalar_llvm_type_at(
        &self,
        ctx: &CodeGenCtx<'_, 'm>,
        scalar: Scalar,
    ) -> llvm::types::AnyTypeEnum<'m>;

    /// Create a type for a [`ScalarKind::Pair`].
    fn scalar_pair_element_llvm_ty(
        &self,
        ctx: &CodeGenCtx<'_, 'm>,
        index: usize,
        immediate: bool,
    ) -> llvm::types::AnyTypeEnum<'m>;
}

impl<'m> ExtendedTyBuilderMethods<'m> for TyInfo {
    fn llvm_ty(&self, ctx: &CodeGenCtx<'_, 'm>) -> llvm::types::AnyTypeEnum<'m> {
        let (abi, variant_index) = self.layout.map(|layout| {
            let variant_index = match &layout.variants {
                Variants::Single { index } => Some(*index),
                _ => None,
            };

            (layout.abi, variant_index)
        });

        // Check the cache if we have already computed the lowered type
        // for this ir-type.
        if let Some(ty_remap) = ctx.ty_remaps.borrow().get(&(self.ty, variant_index)) {
            return ty_remap.ty;
        }

        match abi {
            AbiRepresentation::Scalar(scalar) => self.scalar_llvm_type_at(ctx, scalar),
            AbiRepresentation::Vector { elements, kind } => {
                ctx.type_vector(self.scalar_llvm_type_at(ctx, kind), elements)
            }
            AbiRepresentation::Pair(..) => ctx.type_struct(
                &[
                    self.scalar_pair_element_llvm_ty(ctx, 0, false),
                    self.scalar_pair_element_llvm_ty(ctx, 1, false),
                ],
                false,
            ),

            _ => {
                self.layout.map(|layout| {
                    self.ty.map(|ty| {
                        // Firstly, we want to compute the name of the type that we are going
                        // to create.
                        //
                        // @@Todo: make emitting names optional in order to improve speed
                        // of LLVM builds.
                        let name: Option<String> = match ty {
                            ReprTy::Adt(adt) => {
                                adt.map(|adt| {
                                    // We don't create a name for tuple types, they are just
                                    // regarded
                                    // as opaque structs
                                    if adt.flags.is_tuple() {
                                        return None;
                                    }
                                    let name = adt.name;

                                    // If we have a specific variant for this layout, then we
                                    // can be more precise about the type name..
                                    if let Variants::Single { index } = &layout.variants {
                                        if adt.flags.is_enum() {
                                            return Some(format!(
                                                "{}::{}",
                                                name, adt.variants[*index].name
                                            ));
                                        }
                                    }

                                    Some(format!("{name}"))
                                })
                            }

                            // Everything else is either not a struct or considered to be
                            // opaque.
                            _ => None,
                        };

                        match layout.shape {
                            LayoutShape::Primitive | LayoutShape::Union { .. } => {
                                let fill = ctx.type_padding(layout.size, layout.alignment.abi);
                                let packed = false;

                                match name {
                                    Some(ref name) => {
                                        let ty = ctx.ll_ctx.opaque_struct_type(name);
                                        ty.set_body(&[fill.try_into().unwrap()], packed);

                                        ty.into()
                                    }
                                    None => ctx.type_struct(&[fill], packed),
                                }
                            }
                            LayoutShape::Array { elements, .. } => {
                                // ##Safety: we should be able to assume that `field()` won't create
                                // any new layouts since the layout of the element field should
                                // already be known.
                                let field_ty = self.field(ctx.layouts(), 0).llvm_ty(ctx);
                                ctx.type_array(field_ty, elements)
                            }
                            LayoutShape::Aggregate { .. } => {
                                let (ty, field_remapping) = match name {
                                    Some(ref name) => {
                                        let (fields, packed, new_field_remapping) =
                                            create_and_pad_struct_fields_from_layout(
                                                ctx, *self, layout,
                                            );

                                        let ty = ctx.ll_ctx.opaque_struct_type(name);

                                        // @@Cleanup: we're always fucking converting between
                                        // AnyEnumType and
                                        // BasicEnumType, there must be a better way to do this.
                                        let fields = fields
                                            .into_iter()
                                            .map(|ty| ty.try_into().unwrap())
                                            .collect::<Vec<_>>();

                                        ty.set_body(&fields, packed);
                                        (ty.into(), new_field_remapping)
                                    }
                                    None => {
                                        let (fields, packed, new_field_remapping) =
                                            create_and_pad_struct_fields_from_layout(
                                                ctx, *self, layout,
                                            );

                                        (ctx.type_struct(&fields, packed), new_field_remapping)
                                    }
                                };

                                ctx.ty_remaps.borrow_mut().insert(
                                    (self.ty, variant_index),
                                    TyMemoryRemap { ty, remap: field_remapping },
                                );

                                ty
                            }
                        }
                    })
                })
            }
        }
    }

    fn immediate_llvm_ty(&self, ctx: &CodeGenCtx<'_, 'm>) -> llvm::types::AnyTypeEnum<'m> {
        let is_bool = self.layout.map(
            |layout| matches!(layout.abi, AbiRepresentation::Scalar(scalar) if scalar.is_bool()),
        );

        if is_bool { ctx.type_i1() } else { self.llvm_ty(ctx) }
    }

    fn scalar_llvm_type_at(
        &self,
        ctx: &CodeGenCtx<'_, 'm>,
        scalar: Scalar,
    ) -> llvm::types::AnyTypeEnum<'m> {
        match scalar.kind() {
            ScalarKind::Int { kind, .. } => ctx.type_from_integer(kind),
            ScalarKind::Float { kind } => ctx.type_from_float(kind),
            ScalarKind::Pointer(addr) => ctx.type_ptr_ext(addr),
        }
    }

    fn scalar_pair_element_llvm_ty(
        &self,
        ctx: &CodeGenCtx<'_, 'm>,
        index: usize,
        immediate: bool,
    ) -> llvm::types::AnyTypeEnum<'m> {
        let (scalar_a, scalar_b) = self.layout.map(|layout| {
            let AbiRepresentation::Pair(scalar_a, scalar_b) = layout.abi else {
                panic!("`scalar_pair_element_llvm_ty` called on non-pair type");
            };

            (scalar_a, scalar_b)
        });

        let scalar = if index == 0 { scalar_a } else { scalar_b };

        if immediate && scalar.is_bool() {
            return ctx.type_i1();
        }

        self.scalar_llvm_type_at(ctx, scalar)
    }
}

/// This function will convert a given [Layout] with the shape of an
/// [`LayoutShape::Aggregate`] into a collection of fields that have
/// been padded to the correct alignment and size. In the event that
/// that fields are padded, the `field_map` will be updated to reflect
/// the new field index of the original field.
fn create_and_pad_struct_fields_from_layout<'m>(
    ctx: &CodeGenCtx<'_, 'm>,
    info: TyInfo,
    layout: &Layout,
) -> (Vec<AnyTypeEnum<'m>>, bool, Option<SmallVec<[u32; 4]>>) {
    let field_count = layout.shape.count();

    let mut packed = false;
    let mut offset = Size::ZERO;
    let mut previous_effective_alignment = layout.alignment.abi;

    // Assume that all fields and the last field will need to all be
    // padded.
    let mut fields = Vec::with_capacity(1 + field_count * 2);
    let mut field_map = smallvec![0; field_count];

    for i in layout.shape.iter_increasing_offsets() {
        let target_offset = layout.shape.offset(i);
        let field = info.field(ctx.layouts(), i);

        // @@Todo: maybe re-use the pre-computed padding size here that is available on
        // the layout?
        field.layout.map(|field_layout| {
            let effective_field_align =
                layout.alignment.abi.min(field_layout.alignment.abi).restrict_to(target_offset);
            packed |= effective_field_align < field_layout.alignment.abi;

            let padding = target_offset - offset;
            if padding != Size::ZERO {
                let padding_alignment = previous_effective_alignment.min(effective_field_align);

                // Verify that the padding will make the field aligned.
                debug_assert_eq!(offset.align_to(padding_alignment) + padding, target_offset);

                // Now push the padding into the computed fields
                let fill = ctx.type_padding(padding, padding_alignment);
                fields.push(fill);
            }

            // In the event that we just pushed a pad, we need to update
            // the offset to reflect the new padding.
            field_map[i] = fields.len() as u32;

            fields.push(field.llvm_ty(ctx));
            offset = target_offset + field_layout.size;
            previous_effective_alignment = effective_field_align;
        });
    }

    let fields_padded = fields.len() > field_count;

    if field_count > 0 {
        if offset > layout.size {
            panic!("computed struct fields for LLVM type are larger than the struct itself");
        }

        let padding = layout.size - offset;
        if padding != Size::ZERO {
            let padding_alignment = previous_effective_alignment;

            // Verify that the padding will make the offset equivalent to
            // the layout size.
            debug_assert_eq!(offset.align_to(padding_alignment) + padding, layout.size);

            fields.push(ctx.type_padding(padding, padding_alignment));
        }
    }

    let field_remapping = if fields_padded { Some(field_map) } else { None };

    (fields, packed, field_remapping)
}
