//! This defines the [CodeGenCtx] which is the global context that is
//! used convert Hash IR into LLVM IR, and to perform various other
//! tasks to finalise the LLVM IR and compile it into a native executable.
use std::cell::{Cell, RefCell};

use fxhash::FxHashMap;
use hash_codegen::{
    layout::{compute::LayoutComputer, LayoutCtx},
    symbols::{push_string_encoded_count, ALPHANUMERIC_BASE},
    traits::{ctx::HasCtxMethods, target::HasTargetSpec, Backend, BackendTypes},
};
use hash_ir::{
    ty::{IrTyId, VariantIdx},
    IrCtx,
};
use hash_pipeline::settings::CompilerSettings;
use hash_source::constant::InternedStr;
use hash_target::Target;
use inkwell as llvm;
use llvm::types::AnyTypeEnum;

use crate::translation::ty::TyMemoryRemap;

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

    /// The local symbol counter that is used to generate unique
    /// symbols for the current module.
    pub symbol_counter: Cell<usize>,

    /// A reference to a platform-specific type that represents the width
    /// of pointers and pointer offsets.
    pub size_ty: AnyTypeEnum<'b>,

    /// A collection of [TyMemoryRemap]s that have occurred for
    /// all of the types that have been translated. Additionally, this is used
    /// as a cache to avoid re-lowering [IrTyId]s into the equivalent
    /// LLVM types.
    pub(crate) ty_remaps: RefCell<FxHashMap<(IrTyId, Option<VariantIdx>), TyMemoryRemap<'b>>>,

    /// A map which stores the created [AnyValueEnum]s for the constant
    /// strings [InternedStr] that have been created.
    pub(crate) str_consts: RefCell<FxHashMap<InternedStr, llvm::values::GlobalValue<'b>>>,
}

impl<'b> CodeGenCtx<'b> {
    /// Generate a new local symbol name for the current module.
    pub(crate) fn generate_local_symbol_name(&self, prefix: &str) -> String {
        let symbol_counter = self.symbol_counter.get();
        self.symbol_counter.set(symbol_counter + 1);

        // Since we want to avoid any possible naming conflicts
        // with user defined symbols, we'll add an "illegal" character
        // after the prefix.
        //
        // We add one for the `.` and the rest as anticipation for the
        // symbol counter.
        let mut name = String::with_capacity(prefix.len() + 6);
        name.push_str(prefix);
        name.push('.');
        push_string_encoded_count(symbol_counter as u128, ALPHANUMERIC_BASE, &mut name);

        format!("{prefix}{symbol_counter}")
    }
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
