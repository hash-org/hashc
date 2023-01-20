//! This defines the [CodeGenCtx] which is the global context that is
//! used convert Hash IR into LLVM IR, and to perform various other
//! tasks to finalise the LLVM IR and compile it into a native executable.
use hash_codegen::{
    layout::{compute::LayoutComputer, Layout, LayoutCtx},
    traits::{ctx::HasCtxMethods, target::HasTargetSpec, Backend, BackendTypes},
};
use hash_ir::IrCtx;
use hash_pipeline::settings::CompilerSettings;
use inkwell as llvm;

pub struct CodeGenCtx<'ll> {
    /// The LLVM module that we are putting items into.
    pub module: &'ll llvm::module::Module<'ll>,

    /// The InkWell context that we are generating code with.
    pub ll_ctx: llvm::context::ContextRef<'ll>,
}

impl HasTargetSpec for CodeGenCtx<'_> {
    fn target_spec(&self) -> &hash_target::Target {
        todo!()
    }
}

/// Implement the types for the [CodeGenCtx].
impl<'ll> BackendTypes for CodeGenCtx<'ll> {
    type Value = &'ll llvm::values::AnyValueEnum<'ll>;

    type Function = &'ll llvm::values::FunctionValue<'ll>;

    type Type = &'ll llvm::types::BasicTypeEnum<'ll>;

    type BasicBlock = &'ll llvm::basic_block::BasicBlock<'ll>;

    type DebugInfoScope = &'ll llvm::debug_info::DIScope<'ll>;

    type DebugInfoLocation = &'ll llvm::debug_info::DILocation<'ll>;

    type DebugInfoVariable = &'ll llvm::debug_info::DILocalVariable<'ll>;
}

impl<'b> Backend<'b> for CodeGenCtx<'b> {}

impl<'b> HasCtxMethods<'b> for CodeGenCtx<'b> {
    fn settings(&self) -> &CompilerSettings {
        todo!()
    }

    fn ir_ctx(&self) -> &IrCtx {
        todo!()
    }

    fn layouts(&self) -> &LayoutCtx {
        todo!()
    }

    fn layout_computer(&self) -> LayoutComputer<'_> {
        LayoutComputer::new(self.layouts(), self.ir_ctx())
    }
}

impl<'ll> CodeGenCtx<'ll> {
    pub fn new(module: &'ll llvm::module::Module<'ll>) -> Self {
        Self { module, ll_ctx: module.get_context() }
    }
}
