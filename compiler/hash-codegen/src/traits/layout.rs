//! Trait methods to do with calculating and accessing the layout of types
//! within a backend.

use hash_ir::ty::{IrTy, IrTyId};
use hash_target::layout::HasDataLayout;

use super::BackendTypes;
use crate::layout::TyInfo;

/// Methods for calculating and querying the layout of types within a backend.
pub trait LayoutMethods<'b>: BackendTypes + HasDataLayout {
    /// Compute the layout of a interned type via [IrTyId].
    fn layout_of_id(&self, ty: IrTyId) -> TyInfo;

    /// Compute the layout of a [IrTy].
    fn layout_of(&self, ty: IrTy) -> TyInfo;

    /// Check whether the [TyInfo] layout can be represented as an
    /// immediate value.
    fn is_backend_immediate(&self, ty: TyInfo) -> bool;

    /// Get the type of an element from a sclar pair, and assume
    /// if it "immediate".
    fn scalar_pair_element_backend_type(
        &self,
        info: TyInfo,
        index: usize,
        immediate: bool,
    ) -> Self::Type;
}
