//! This defines the [CodeGenCtx] which is the global context that is
//! used convert Hash IR into LLVM IR, and to perform various other
//! tasks to finalise the LLVM IR and compile it into a native executable.
use std::cell::{Cell, RefCell};

use fxhash::FxHashMap;
use hash_codegen::{
    layout::{compute::LayoutComputer, LayoutCtx},
    symbols::{push_string_encoded_count, ALPHANUMERIC_BASE},
    traits::{BackendTypes, HasCtxMethods},
};
use hash_ir::{
    ty::{InstanceId, IrTyId, VariantIdx},
    IrCtx,
};
use hash_pipeline::settings::CompilerSettings;
use hash_source::constant::InternedStr;
use inkwell as llvm;
use llvm::values::FunctionValue;

use crate::translation::ty::TyMemoryRemap;

/// The [CodeGenCtx] is used a context for converting Hash IR into LLVM IR. It
/// stores references to all of the required information about the IR, as well
/// as several stores in order to reduce the amount of work that is required to
/// translate the IR.
pub struct CodeGenCtx<'b, 'm> {
    /// The Compiler settings that is being used for the current
    /// session.
    pub settings: &'b CompilerSettings,

    /// A reference to the IR context.
    pub ir_ctx: &'b IrCtx,

    /// Store for all of the information about type [Layout]s.
    pub layouts: &'b LayoutCtx,

    /// The LLVM module that we are putting items into.
    pub module: &'b llvm::module::Module<'m>,

    /// The LLVM "context" that is used for building and
    /// translating into LLVM IR.
    pub ll_ctx: llvm::context::ContextRef<'m>,

    /// The local symbol counter that is used to generate unique
    /// symbols for the current module.
    pub symbol_counter: Cell<usize>,

    /// A reference to a platform-specific type that represents the width
    /// of pointers and pointer offsets.
    pub size_ty: llvm::types::IntType<'m>,

    /// A mapping between [InstanceId]s to [FunctionValue]s in order
    /// to avoid re-generating declaring instance references.
    pub(crate) instances: RefCell<FxHashMap<InstanceId, llvm::values::FunctionValue<'m>>>,

    /// A collection of [TyMemoryRemap]s that have occurred for
    /// all of the types that have been translated. Additionally, this is used
    /// as a cache to avoid re-lowering [IrTyId]s into the equivalent
    /// LLVM types.
    pub(crate) ty_remaps: RefCell<FxHashMap<(IrTyId, Option<VariantIdx>), TyMemoryRemap<'m>>>,

    /// A map which stores the created [AnyValueEnum]s for the constant
    /// strings [InternedStr] that have been created.
    pub(crate) str_consts: RefCell<FxHashMap<InternedStr, llvm::values::GlobalValue<'m>>>,

    /// A map that stores all of the used intrinsics within the current module
    /// context. These intrinsics are computed as they are required (when
    /// referenced within the source).
    ///
    /// This maps the name of the intrinsic which is known at compile-time to
    /// the corresponding function pointer value, and the type of the
    /// intrinsic.
    pub(crate) intrinsics: RefCell<FxHashMap<&'static str, FunctionValue<'m>>>,
}

impl<'b, 'm> CodeGenCtx<'b, 'm> {
    /// Create a new [CodeGenCtx].
    pub fn new(
        module: &'b llvm::module::Module<'m>,
        settings: &'b CompilerSettings,
        ir_ctx: &'b IrCtx,
        layouts: &'b LayoutCtx,
    ) -> Self {
        let ptr_size = layouts.data_layout.pointer_size;
        let ll_ctx = module.get_context();

        let size_ty = ll_ctx.custom_width_int_type(ptr_size.bits() as u32);

        Self {
            settings,
            ir_ctx,
            layouts,
            module,
            ll_ctx,
            symbol_counter: Cell::new(0),
            size_ty,
            instances: RefCell::new(FxHashMap::default()),
            ty_remaps: RefCell::new(FxHashMap::default()),
            str_consts: RefCell::new(FxHashMap::default()),
            intrinsics: RefCell::new(FxHashMap::default()),
        }
    }

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
        name
    }
}

/// Implement the types for the [CodeGenCtx].
impl<'b, 'm> BackendTypes for CodeGenCtx<'b, 'm> {
    type Value = llvm::values::AnyValueEnum<'m>;

    type Function = llvm::values::FunctionValue<'m>;

    type Type = llvm::types::AnyTypeEnum<'m>;

    type BasicBlock = llvm::basic_block::BasicBlock<'m>;

    type DebugInfoScope = llvm::debug_info::DIScope<'m>;

    type DebugInfoLocation = llvm::debug_info::DILocation<'m>;

    type DebugInfoVariable = llvm::debug_info::DILocalVariable<'m>;
}

impl<'b> HasCtxMethods<'b> for CodeGenCtx<'b, '_> {
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
