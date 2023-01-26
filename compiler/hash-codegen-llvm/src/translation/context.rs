//! This defines the [CodeGenCtx] which is the global context that is
//! used convert Hash IR into LLVM IR, and to perform various other
//! tasks to finalise the LLVM IR and compile it into a native executable.
use std::cell::RefCell;

use fxhash::FxHashMap;
use hash_codegen::{
    layout::{compute::LayoutComputer, Layout, LayoutCtx},
    traits::{ctx::HasCtxMethods, target::HasTargetSpec, Backend, BackendTypes},
};
use hash_ir::{
    ty::{IrTyId, VariantIdx},
    IrCtx,
};
use hash_pipeline::settings::CompilerSettings;
use hash_target::{data_layout::TargetDataLayout, Target};
use inkwell as llvm;

use super::ty::TyMemoryRemap;

pub struct CodeGenCtx<'b> {
    /// The Compiler settings that is being used for the current
    /// session.
    pub settings: &'b CompilerSettings,

    /// A reference to the IR context.
    pub ir_ctx: &'b IrCtx,

    /// Store for all of the information about type [Layout]s.
    pub layouts: &'b LayoutCtx,

    /// The LLVM module that we are putting items into.
    pub module: &'b llvm::module::Module<'b>,

    /// The LLVM "context" that is used for building and
    /// translating into LLVM IR.
    pub ll_ctx: llvm::context::ContextRef<'b>,

    /// A collection of [TyMemoryRemap]s that have occurred for
    /// all of the types that have been translated. Additionally, this is used
    /// as a cache to avoid re-lowering [IrTyId]s into the equivalent
    /// LLVM types.
    pub(crate) ty_remaps: RefCell<FxHashMap<(IrTyId, Option<VariantIdx>), TyMemoryRemap<'b>>>,
}

impl HasTargetSpec for CodeGenCtx<'_> {
    fn target_spec(&self) -> &Target {
        self.settings.codegen_settings.target_info.target()
    }
}

/// Implement the types for the [CodeGenCtx].
impl<'ll> BackendTypes for CodeGenCtx<'ll> {
    type Value = llvm::values::AnyValueEnum<'ll>;

    type Function = llvm::values::FunctionValue<'ll>;

    type Type = llvm::types::AnyTypeEnum<'ll>;

    type BasicBlock = llvm::basic_block::BasicBlock<'ll>;

    type DebugInfoScope = llvm::debug_info::DIScope<'ll>;

    type DebugInfoLocation = llvm::debug_info::DILocation<'ll>;

    type DebugInfoVariable = llvm::debug_info::DILocalVariable<'ll>;
}

impl<'b> Backend<'b> for CodeGenCtx<'b> {}

impl<'b> HasCtxMethods<'b> for CodeGenCtx<'b> {
    fn settings(&self) -> &CompilerSettings {
        self.settings
    }

    fn ir_ctx(&self) -> &IrCtx {
        self.ir_ctx
    }

    fn layouts(&self) -> &LayoutCtx {
        self.layouts
    }

    fn layout_computer(&self) -> LayoutComputer<'_> {
        LayoutComputer::new(self.layouts(), self.ir_ctx())
    }
}
