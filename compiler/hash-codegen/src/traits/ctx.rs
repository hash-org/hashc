//! Defines an interface for accessing the context from pre-codegen
//! stages of the compiler in order to perform code generation. The
//! context is used to access information about types, layouts, and
//! other information that is required for code generation.

use hash_ir::{
    ty::{IrTy, IrTyId},
    IrCtx,
};
use hash_layout::{LayoutCtx, LayoutStore};
use hash_pipeline::settings::CompilerSettings;
use hash_target::layout::HasDataLayout;

use crate::layout::{Layout, LayoutId};

pub trait HasCtxMethods<'b>: HasDataLayout {
    /// Return a reference to the current [CompilerSettings] for the
    /// workspace.
    fn settings(&self) -> &CompilerSettings;

    /// Returns a reference to the IR [IrCtx].
    fn ir_ctx(&self) -> &IrCtx;

    /// Create a [LayoutCtx]
    fn layout_ctx(&self) -> LayoutCtx<'_> {
        LayoutCtx::new(self.layouts(), self.data_layout(), self.ir_ctx())
    }

    /// Returns a reference to an IR type from the context.
    fn ty_info(&self, ty: IrTyId) -> &IrTy;

    /// Returns a reference to the underling [Layout] information for a
    /// particular [LayoutId].
    fn layout_info(&self, layout: LayoutId) -> &Layout;

    /// Returns a reference to the [LayoutStore].
    fn layouts(&self) -> &LayoutStore;
}
