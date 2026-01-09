//! Implements all of the required methods for computing the layouts of types.

use hash_codegen::{repr::TyInfo, target::abi::AbiRepresentation, traits::layout::LayoutMethods};
use hash_storage::store::statics::StoreId;

use crate::{ctx::Ctx, translation::VMBuilder};

impl<'b> LayoutMethods<'b> for Ctx<'b> {
    fn is_backend_immediate(&self, info: TyInfo) -> bool {
        info.layout.map(|layout| layout.is_vm_immediate())
    }

    fn is_backend_scalar_pair(&self, info: TyInfo) -> bool {
        info.layout.map(|layout| layout.is_vm_scalar_pair())
    }
}

impl<'b> LayoutMethods<'b> for VMBuilder<'_, 'b> {
    fn is_backend_immediate(&self, info: TyInfo) -> bool {
        self.ctx.is_backend_immediate(info)
    }

    fn is_backend_scalar_pair(&self, info: TyInfo) -> bool {
        self.ctx.is_backend_scalar_pair(info)
    }
}

pub trait ExtendedLayoutMethods<'m> {
    fn is_vm_immediate(&self) -> bool;

    /// Returns true if this [Layout] ABI is represented as is a
    /// [`AbiRepresentation::Pair`]
    fn is_vm_scalar_pair(&self) -> bool;
}

impl<'m> ExtendedLayoutMethods<'m> for &hash_codegen::repr::Layout {
    fn is_vm_immediate(&self) -> bool {
        match self.abi {
            AbiRepresentation::Scalar(_) | AbiRepresentation::Vector { .. } => true,
            AbiRepresentation::Pair(..)
            | AbiRepresentation::Aggregate
            | AbiRepresentation::Uninhabited => false,
        }
    }

    fn is_vm_scalar_pair(&self) -> bool {
        matches!(self.abi, hash_codegen::target::abi::AbiRepresentation::Pair(..))
    }
}
