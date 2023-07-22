//! Trait methods to do with calculating and accessing the layout of types
//! within a backend.

use hash_ir::ty::IrTyId;
use hash_layout::{Layout, LayoutId};
use hash_storage::store::Store;

use super::{BackendTypes, HasCtxMethods};
use crate::layout::TyInfo;

/// Methods for calculating and querying the layout of types within a backend.
pub trait LayoutMethods<'b>: BackendTypes + HasCtxMethods<'b> {
    /// Compute the layout of a interned type via [IrTyId].
    fn layout_of(&self, ty: IrTyId) -> TyInfo {
        // @@Todo: provide a mechanism for gracefully reporting the error rather
        // than unwrapping
        let layout = self.layout_computer().layout_of_ty(ty).unwrap();
        TyInfo { ty, layout }
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
}
