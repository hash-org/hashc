//! Trait methods to do with calculating and accessing the layout of types
//! within a backend.

use hash_ir::ty::{IrTy, IrTyId};
use hash_layout::{Layout, LayoutId};
use hash_utils::store::Store;

use super::{ctx::HasCtxMethods, BackendTypes};
use crate::layout::TyInfo;

/// Methods for calculating and querying the layout of types within a backend.
pub trait LayoutMethods<'b>: BackendTypes + HasCtxMethods<'b> {
    /// Compute the layout of a interned type via [IrTyId].
    fn layout_of_id(&self, _ty: IrTyId) -> TyInfo {
        todo!()
    }

    /// Compute the layout of a [IrTy].
    fn layout_of(&self, _ty: IrTy) -> TyInfo {
        todo!()
    }

    /// Perform a mapping on a [Layout]
    fn map_layout<T>(&self, id: LayoutId, func: impl FnOnce(&Layout) -> T) -> T {
        self.layouts().map_fast(id, func)
    }

    /// Compute the field index from the backend specific type.
    fn backend_field_index(&self, info: TyInfo, index: usize) -> u64;

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
