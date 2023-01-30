//! Implements all of the required methods for computing the layouts of types.

use hash_codegen::{
    layout::{Layout, LayoutShape, TyInfo, Variants},
    traits::layout::LayoutMethods,
};
use hash_ir::{ty::IrTyId, write::WriteIr};
use hash_target::{
    abi::AbiRepresentation,
    data_layout::{HasDataLayout, TargetDataLayout},
};

use super::{
    ty::{ExtendedTyBuilderMethods, TyMemoryRemap},
    Builder,
};
use crate::context::CodeGenCtx;

impl<'b> LayoutMethods<'b> for CodeGenCtx<'b> {
    fn backend_field_index(&self, info: TyInfo, index: usize) -> u64 {
        self.map_layout(info.layout, |layout| layout.llvm_field_index(self, info.ty, index))
    }

    fn is_backend_immediate(&self, info: TyInfo) -> bool {
        self.map_layout(info.layout, |layout| layout.is_llvm_immediate())
    }

    fn scalar_pair_element_backend_type(
        &self,
        info: TyInfo,
        index: usize,
        immediate: bool,
    ) -> Self::Type {
        info.scalar_pair_element_llvm_ty(self, index, immediate)
    }
}

impl HasDataLayout for CodeGenCtx<'_> {
    fn data_layout(&self) -> &TargetDataLayout {
        &self.settings.codegen_settings.data_layout
    }
}

impl<'b> LayoutMethods<'b> for Builder<'b> {
    fn backend_field_index(&self, info: TyInfo, index: usize) -> u64 {
        self.ctx.backend_field_index(info, index)
    }

    fn is_backend_immediate(&self, ty: TyInfo) -> bool {
        self.ctx.is_backend_immediate(ty)
    }

    fn scalar_pair_element_backend_type(
        &self,
        info: TyInfo,
        index: usize,
        immediate: bool,
    ) -> Self::Type {
        self.ctx.scalar_pair_element_backend_type(info, index, immediate)
    }
}

impl HasDataLayout for Builder<'_> {
    fn data_layout(&self) -> &TargetDataLayout {
        self.ctx.data_layout()
    }
}

pub trait ExtendedLayoutMethods<'b> {
    /// Compute the field index from the backend specific type.
    fn llvm_field_index(&self, cx: &CodeGenCtx<'b>, ty: IrTyId, index: usize) -> u64;

    /// Check if this is type is represented as an immediate value.
    fn is_llvm_immediate(&self) -> bool;

    /// Returns true if this [Layout] ABI is represented as is a
    /// [`AbiRepresentation::Pair(..)`]
    fn is_llvm_scalar_pair(&self) -> bool;
}

impl<'b> ExtendedLayoutMethods<'b> for &Layout {
    fn is_llvm_immediate(&self) -> bool {
        match self.abi {
            AbiRepresentation::Scalar(_) | AbiRepresentation::Vector { .. } => true,
            AbiRepresentation::Pair(..) => false,
            AbiRepresentation::Aggregate { .. } | AbiRepresentation::Uninhabited => self.is_zst(),
        }
    }

    fn is_llvm_scalar_pair(&self) -> bool {
        matches!(self.abi, AbiRepresentation::Pair(..))
    }

    fn llvm_field_index(&self, ctx: &CodeGenCtx<'b>, ty: IrTyId, index: usize) -> u64 {
        // Field index of scalar and scalar pairs is not applicable since
        // it is handled else where.
        match self.abi {
            AbiRepresentation::Scalar(_) | AbiRepresentation::Pair(..) => {
                panic!("cannot get field index of scalar or scalar pair")
            }
            _ => {}
        };

        match self.shape {
            LayoutShape::Primitive | LayoutShape::Union { .. } => {
                panic!("cannot get field index of primitive or union")
            }
            LayoutShape::Array { .. } => index as u64,

            // Here, we have to rely on the re-mapped version of the layout since
            // we had to adjust it to account for all of the padding that was added
            // to the struct/aggregate.
            LayoutShape::Aggregate { .. } => {
                let variant_index = match self.variants {
                    Variants::Single { index } => Some(index),
                    Variants::Multiple { .. } => None,
                };

                match ctx.ty_remaps.borrow().get(&(ty, variant_index)) {
                    Some(TyMemoryRemap { remap: Some(ref remap), .. }) => remap[index] as u64,
                    Some(TyMemoryRemap { remap: None, .. }) => {
                        self.shape.memory_index(index) as u64
                    }
                    None => panic!("cannot find remapped layout for `{}`", ty.for_fmt(ctx.ir_ctx)),
                }
            }
        }
    }
}
