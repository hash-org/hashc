//! Context for building bytecode bodies from Hash IR.

use hash_codegen::{
    backend::CodeGenStorage,
    repr::{LayoutStorage, compute::LayoutComputer},
    target::{HasTarget, Target},
    traits::{BackendTypes, HasCtxMethods},
};
use hash_ir::IrCtx;
use hash_pipeline::settings::CompilerSettings;

/// The [Ctx] is used a context for converting Hash IR into bytecode. It
/// stores references to all of the required information about the IR, as well
/// as several stores in order to reduce the amount of work that is required to
/// translate the IR.
pub struct Ctx<'a> {
    /// The Compiler settings that is being used for the current
    /// session.
    pub settings: &'a CompilerSettings,

    /// A reference to the IR context.
    pub ir_ctx: &'a IrCtx,

    /// A reference to the code generation context.
    pub codegen_ctx: &'a CodeGenStorage,

    /// Store for all of the information about type [Layout]s.
    pub layouts: &'a LayoutStorage,

    /// The bytecode builder that is being used to build the bytecode.
    pub builder: builder::BytecodeBuilder,
}

impl Ctx<'_> {
    /// Create a new [Ctx] from the given components.
    pub fn new<'a>(
        settings: &'a CompilerSettings,
        ir_ctx: &'a IrCtx,
        codegen_ctx: &'a CodeGenStorage,
        layouts: &'a LayoutStorage,
    ) -> Ctx<'a> {
        Ctx { settings, ir_ctx, codegen_ctx, layouts, builder: builder::BytecodeBuilder::new() }
    }
}

/// Specification for `BackedTypes` for the [Ctx].
impl<'m> BackendTypes for Ctx<'m> {
    type Value = ();
    type Function = ();
    type Type = ();
    type BasicBlock = ();
    type DebugInfoScope = ();
    type DebugInfoLocation = ();
    type DebugInfoVariable = ();
}

impl HasTarget for Ctx<'_> {
    fn target(&self) -> &Target {
        self.settings.target()
    }
}

impl<'b> HasCtxMethods<'b> for Ctx<'b> {
    fn settings(&self) -> &CompilerSettings {
        self.settings
    }

    fn ir_ctx(&self) -> &IrCtx {
        self.ir_ctx
    }

    fn layouts(&self) -> LayoutComputer<'_> {
        LayoutComputer::new(self.layouts)
    }

    fn cg_ctx(&self) -> &CodeGenStorage {
        self.codegen_ctx
    }
}
