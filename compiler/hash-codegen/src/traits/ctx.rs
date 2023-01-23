//! Defines an interface for accessing the context from pre-codegen
//! stages of the compiler in order to perform code generation. The
//! context is used to access information about types, layouts, and
//! other information that is required for code generation.

use hash_ir::IrCtx;
use hash_layout::{compute::LayoutComputer, LayoutCtx};
use hash_pipeline::settings::CompilerSettings;
use hash_target::data_layout::HasDataLayout;

pub trait HasCtxMethods<'b>: HasDataLayout {
    /// Return a reference to the current [CompilerSettings] for the
    /// workspace.
    fn settings(&self) -> &CompilerSettings;

    /// Returns a reference to the IR [IrCtx].
    fn ir_ctx(&self) -> &IrCtx;

    /// Create a [LayoutComputer] for the current context.
    fn layout_computer(&self) -> LayoutComputer<'_> {
        LayoutComputer::new(self.layouts(), self.ir_ctx())
    }

    /// Returns a reference to the [LayoutStore].
    fn layouts(&self) -> &LayoutCtx;
}
