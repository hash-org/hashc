//! Translation sources of mapping Hash IR to Hash VM bytecode.

mod abi;
mod builder;
mod constants;
mod debug_info;
mod intrinsics;
mod layouts;
mod misc;
mod statics;
mod ty;

use hash_codegen::{
    backend::CodeGenStorage,
    repr::compute::LayoutComputer,
    target::{HasTarget, Target},
    traits::{BackendTypes, Codegen, HasCtxMethods},
};
use hash_ir::IrCtx;
use hash_pipeline::settings::CompilerSettings;

use crate::ctx::Ctx;

/// The [VMBuilder] is the main builder type for generating Hash VM bytecode.
///
/// It provides access to the code generation context, target information,
/// and various utilities needed during the translation process.
///
/// The [VMBuilder] implements all of the traits that are required for code
/// generation to occur. This includes traits for handling ABI methods, type
/// layouts, and other codegen-related functionality.
pub struct VMBuilder<'a, 'b> {
    /// The context for the builder.
    pub(crate) ctx: &'a Ctx<'b>,
}

impl<'b> Codegen<'b> for VMBuilder<'_, 'b> {
    type CodegenCtx = Ctx<'b>;
}

impl<'b> BackendTypes for VMBuilder<'_, 'b> {
    type Value = <Ctx<'b> as BackendTypes>::Value;
    type Function = <Ctx<'b> as BackendTypes>::Function;
    type Type = <Ctx<'b> as BackendTypes>::Type;
    type BasicBlock = <Ctx<'b> as BackendTypes>::BasicBlock;
    type DebugInfoScope = <Ctx<'b> as BackendTypes>::DebugInfoScope;
    type DebugInfoLocation = <Ctx<'b> as BackendTypes>::DebugInfoLocation;
    type DebugInfoVariable = <Ctx<'b> as BackendTypes>::DebugInfoVariable;
}

impl<'a, 'b> std::ops::Deref for VMBuilder<'a, 'b> {
    type Target = Ctx<'b>;

    fn deref(&self) -> &Self::Target {
        self.ctx
    }
}

impl HasTarget for VMBuilder<'_, '_> {
    fn target(&self) -> &Target {
        self.ctx.target()
    }
}

impl<'b> HasCtxMethods<'b> for VMBuilder<'_, 'b> {
    fn settings(&self) -> &CompilerSettings {
        self.ctx.settings()
    }

    fn ir_ctx(&self) -> &IrCtx {
        self.ctx.ir_ctx()
    }

    fn layouts(&self) -> LayoutComputer<'_> {
        self.ctx.layouts()
    }

    fn cg_ctx(&self) -> &CodeGenStorage {
        self.ctx.cg_ctx()
    }
}
