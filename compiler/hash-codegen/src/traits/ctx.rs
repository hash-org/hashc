//! Defines an interface for accessing the context from pre-codegen
//! stages of the compiler in order to perform code generation. The
//! context is used to access information about types, layouts, and
//! other information that is required for code generation.

use hash_ir::ty::{IrTy, IrTyId};
use hash_target::layout::HasDataLayout;

use crate::layout::{Layout, LayoutId};

pub trait HasCtxMethods<'b>: HasDataLayout {
    /// Returns a reference to an IR type from the context.
    fn ty_info(&self, ty: IrTyId) -> &IrTy;

    /// Returns a reference to the underling [Layout] information for a
    /// particular [LayoutId].
    fn layout_info(&self, layout: LayoutId) -> &Layout;
}