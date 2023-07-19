//! Implements all of the required methods for computing the layouts of types.

use hash_codegen::{
    layout::{Layout, LayoutShape, TyInfo, Variants},
    target::{
        abi::AbiRepresentation,
        data_layout::{HasDataLayout, TargetDataLayout},
    },
    traits::layout::LayoutMethods,
};
use hash_ir::ty::IrTyId;

use super::{ty::TyMemoryRemap, LLVMBuilder};
use crate::ctx::CodeGenCtx;

impl<'b> LayoutMethods<'b> for CodeGenCtx<'b, '_> {
    fn backend_field_index(&self, info: TyInfo, index: usize) -> u64 {
        self.map_layout(info.layout, |layout| layout.llvm_field_index(self, info.ty, index))
    }

    fn is_backend_immediate(&self, info: TyInfo) -> bool {
        self.map_layout(info.layout, |layout| layout.is_llvm_immediate())
    }
}

impl HasDataLayout for CodeGenCtx<'_, '_> {
    fn data_layout(&self) -> &TargetDataLayout {
        &self.layouts.data_layout
    }
}

impl<'b, 'm> LayoutMethods<'b> for LLVMBuilder<'_, 'b, 'm> {
    fn backend_field_index(&self, info: TyInfo, index: usize) -> u64 {
        self.ctx.backend_field_index(info, index)
    }

    fn is_backend_immediate(&self, ty: TyInfo) -> bool {
        self.ctx.is_backend_immediate(ty)
    }
}

impl HasDataLayout for LLVMBuilder<'_, '_, '_> {
    fn data_layout(&self) -> &TargetDataLayout {
        self.ctx.data_layout()
    }
}

pub trait ExtendedLayoutMethods<'m> {
    /// Compute the field index from the backend specific type.
    fn llvm_field_index(&self, cx: &CodeGenCtx<'_, 'm>, ty: IrTyId, index: usize) -> u64;

    /// Check if this is type is represented as an immediate value.
    fn is_llvm_immediate(&self) -> bool;

    /// Returns true if this [Layout] ABI is represented as is a
    /// [`AbiRepresentation::Pair(..)`]
    fn is_llvm_scalar_pair(&self) -> bool;
}

impl<'m> ExtendedLayoutMethods<'m> for &Layout {
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

    fn llvm_field_index(&self, ctx: &CodeGenCtx<'_, 'm>, ty: IrTyId, index: usize) -> u64 {
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
                    None => panic!("cannot find remapped layout for `{}`", ty),
                }
            }
        }
    }
}
