//! Trait methods to do with calculating and accessing the layout of types
//! within a backend.

use hash_ir::ty::IrTy;
use hash_target::layout::HasDataLayout;

use super::BackendTypes;
use crate::layout::TyInfo;

/// Methods for calculating and querying the layout of types within a backend.
pub trait LayoutMethods<'b>: BackendTypes + HasDataLayout {
    /// Compute the layout of a specific type.
    fn layout_of(&self, ty: &IrTy) -> TyInfo;
}
