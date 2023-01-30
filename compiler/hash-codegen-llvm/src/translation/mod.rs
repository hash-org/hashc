//! Hash compiler LLVM code generation crate. This crate contains all of the
//! logic of transforming generated Hash IR into LLVM IR so that it can be
//! compiled by LLVM into a native executable with the specified target triple.

use hash_codegen::{
    layout::{compute::LayoutComputer, LayoutCtx},
    traits::{ctx::HasCtxMethods, target::HasTargetSpec, Backend, BackendTypes, Codegen},
};
use hash_ir::IrCtx;
use hash_pipeline::settings::CompilerSettings;
use hash_target::Target;

use crate::context::CodeGenCtx;

mod abi;
mod builder;
mod constants;
mod debug_info;
mod declare;
mod intrinsics;
mod layouts;
mod metadata;
mod misc;
pub(crate) mod ty;

/// A [Builder] is defined as being a context that is used to implement
/// all of the specified builder methods.
pub struct Builder<'b> {
    /// The actual InkWell builder
    builder: inkwell::builder::Builder<'b>,

    /// The context for the builder.
    ctx: &'b CodeGenCtx<'b>,
}

/// This specifies that the [Builder] context is [CodeGenCtx].
impl<'b> Codegen<'b> for Builder<'b> {
    type CodegenCtx = CodeGenCtx<'b>;
}

/// This specifies all of the common IR type kinds for [Builder].
impl<'b> BackendTypes for Builder<'b> {
    type Value = <CodeGenCtx<'b> as BackendTypes>::Value;
    type Function = <CodeGenCtx<'b> as BackendTypes>::Function;
    type Type = <CodeGenCtx<'b> as BackendTypes>::Type;
    type BasicBlock = <CodeGenCtx<'b> as BackendTypes>::BasicBlock;

    type DebugInfoScope = <CodeGenCtx<'b> as BackendTypes>::DebugInfoScope;
    type DebugInfoLocation = <CodeGenCtx<'b> as BackendTypes>::DebugInfoLocation;
    type DebugInfoVariable = <CodeGenCtx<'b> as BackendTypes>::DebugInfoVariable;
}

impl<'b> Backend<'b> for Builder<'b> {}

impl<'b> std::ops::Deref for Builder<'b> {
    type Target = CodeGenCtx<'b>;

    fn deref(&self) -> &Self::Target {
        self.ctx
    }
}

impl<'b> HasCtxMethods<'b> for Builder<'b> {
    fn settings(&self) -> &CompilerSettings {
        self.ctx.settings()
    }

    fn ir_ctx(&self) -> &IrCtx {
        self.ctx.ir_ctx()
    }

    fn layouts(&self) -> &LayoutCtx {
        self.ctx.layouts()
    }

    fn layout_computer(&self) -> LayoutComputer<'_> {
        self.ctx.layout_computer()
    }
}

impl HasTargetSpec for Builder<'_> {
    fn target_spec(&self) -> &Target {
        self.ctx.target_spec()
    }
}
