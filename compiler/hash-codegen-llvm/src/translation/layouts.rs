//! Implements all of the required methods for computing the layouts of types.

use hash_codegen::{
    repr::{Layout, TyInfo},
    target::abi::AbiRepresentation,
    traits::layout::LayoutMethods,
};
use hash_storage::store::statics::StoreId;

use super::LLVMBuilder;
use crate::ctx::CodeGenCtx;

impl<'b> LayoutMethods<'b> for CodeGenCtx<'b, '_> {
    fn is_backend_immediate(&self, info: TyInfo) -> bool {
        info.layout.map(|layout| layout.is_llvm_immediate())
    }

    fn is_backend_scalar_pair(&self, info: TyInfo) -> bool {
        info.layout.map(|layout| layout.is_llvm_scalar_pair())
    }
}

impl<'b> LayoutMethods<'b> for LLVMBuilder<'_, 'b, '_> {
    fn is_backend_immediate(&self, ty: TyInfo) -> bool {
        self.ctx.is_backend_immediate(ty)
    }

    fn is_backend_scalar_pair(&self, ty: TyInfo) -> bool {
        self.ctx.is_backend_scalar_pair(ty)
    }
}

pub trait ExtendedLayoutMethods<'m> {
    /// Check if this is type is represented as an immediate value.
    fn is_llvm_immediate(&self) -> bool;

    /// Returns true if this [Layout] ABI is represented as is a
    /// [`AbiRepresentation::Pair`]
    fn is_llvm_scalar_pair(&self) -> bool;
}

impl<'m> ExtendedLayoutMethods<'m> for &Layout {
    fn is_llvm_immediate(&self) -> bool {
        match self.abi {
            AbiRepresentation::Scalar(_) | AbiRepresentation::Vector { .. } => true,
            AbiRepresentation::Pair(..) => false,
            AbiRepresentation::Aggregate | AbiRepresentation::Uninhabited => self.is_zst(),
        }
    }

    fn is_llvm_scalar_pair(&self) -> bool {
        matches!(self.abi, AbiRepresentation::Pair(..))
    }
}
