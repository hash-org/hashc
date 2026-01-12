//! Hash compiler LLVM code generation crate. This crate contains all of the
//! logic of transforming generated Hash IR into LLVM IR so that it can be
//! compiled by LLVM into a native executable with the specified target triple.

use std::ffi::{CStr, c_char};

use hash_codegen::{
    backend::CodeGenStorage,
    repr::compute::LayoutComputer,
    target::{HasTarget, Target},
    traits::{BackendTypes, Codegen, HasCtxMethods},
};
use hash_ir::IrCtx;
use hash_pipeline::settings::CompilerSettings;

use crate::ctx::CodeGenCtx;

mod abi;
mod builder;
mod constants;
mod debug_info;
mod declare;
mod intrinsics;
mod layouts;
mod metadata;
mod misc;
mod statics;
pub(crate) mod ty;

/// An empty c-string.
const EMPTY_C_STR: &CStr = c"";

/// Used to fill in names where LLVM requires a name for an instruction, or some
/// value. We don't care about the names, so we just use an empty c-string.
pub(crate) const EMPTY_NAME: *const c_char = EMPTY_C_STR.as_ptr();

/// A [Builder] is defined as being a context that is used to implement
/// all of the specified builder methods.
pub struct LLVMBuilder<'a, 'b, 'm> {
    /// The actual Inkwell builder.
    pub(crate) builder: inkwell::builder::Builder<'m>,

    /// The context for the builder.
    pub(crate) ctx: &'a CodeGenCtx<'b, 'm>,
}

/// This specifies that the [LLVMBuilder] context is [CodeGenCtx].
impl<'b, 'm> Codegen<'b> for LLVMBuilder<'_, 'b, 'm> {
    type CodegenCtx = CodeGenCtx<'b, 'm>;
}

/// This specifies all of the common IR type kinds for [Builder].
impl<'b, 'm> BackendTypes for LLVMBuilder<'_, 'b, 'm> {
    type Value = <CodeGenCtx<'b, 'm> as BackendTypes>::Value;
    type Function = <CodeGenCtx<'b, 'm> as BackendTypes>::Function;
    type Type = <CodeGenCtx<'b, 'm> as BackendTypes>::Type;
    type BasicBlock = <CodeGenCtx<'b, 'm> as BackendTypes>::BasicBlock;
    type DebugInfoScope = <CodeGenCtx<'b, 'm> as BackendTypes>::DebugInfoScope;
    type DebugInfoLocation = <CodeGenCtx<'b, 'm> as BackendTypes>::DebugInfoLocation;
    type DebugInfoVariable = <CodeGenCtx<'b, 'm> as BackendTypes>::DebugInfoVariable;
}

impl<'b, 'm> std::ops::Deref for LLVMBuilder<'_, 'b, 'm> {
    type Target = CodeGenCtx<'b, 'm>;

    fn deref(&self) -> &Self::Target {
        self.ctx
    }
}

impl HasTarget for LLVMBuilder<'_, '_, '_> {
    fn target(&self) -> &Target {
        self.ctx.target()
    }
}

impl<'b> HasCtxMethods<'b> for LLVMBuilder<'_, 'b, '_> {
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
