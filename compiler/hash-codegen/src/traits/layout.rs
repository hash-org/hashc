//! Trait methods to do with calculating and accessing the layout of types
//! within a backend.

use hash_ir::ty::ReprTyId;

use super::{BackendTypes, HasCtxMethods};
use crate::repr::TyInfo;

/// Methods for calculating and querying the layout of types within a backend.
pub trait LayoutMethods<'b>: BackendTypes + HasCtxMethods<'b> {
    /// Compute the layout of a interned type via [ReprTyId].
    fn layout_of(&self, ty: ReprTyId) -> TyInfo {
        // @@Todo: provide a mechanism for gracefully reporting the error rather
        // than unwrapping
        let layout = self.layouts().layout_of_ty(ty).unwrap();
        TyInfo { ty, layout }
    }

    /// Check whether the [TyInfo] layout can be represented as an
    /// immediate value.
    fn is_backend_immediate(&self, ty: TyInfo) -> bool;

    /// Check whether the [TyInfo] layout can be represented as a
    /// backend scalar pair.
    fn is_backend_scalar_pair(&self, ty: TyInfo) -> bool;
}
