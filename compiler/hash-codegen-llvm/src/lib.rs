//! The LLVM code generation backend for Hash. This implements the [Backend]
//! trait that provides an interface between a code generation backend and the
//! actual compiler pipeline, the [BackendCtx] trait which provides an interface
//! between the backend and the compiler context, and the [LLVMBackend] struct
//! which is the actual implementation of the LLVM backend. It is expected that
//! the backend performs it's work in the [LLVMBackend::run] method, and saves
//! the results of each module in the [Workspace].
#![feature(let_chains, hash_raw_entry)]
#![allow(unused)]

use std::{cell::RefCell, path::PathBuf};

use context::CodeGenCtx;
use fxhash::FxHashMap;
use hash_codegen::{
    backend::{Backend, BackendCtx},
    layout::LayoutCtx,
    lower::codegen_ir_body,
};
use hash_ir::{
    ir::BodySource,
    ty::{IrTy, IrTyId},
    IrStorage,
};
use hash_pipeline::{settings::CompilerSettings, workspace::Workspace, CompilerResult};
use hash_source::ModuleId;
use hash_target::TargetArch;
use hash_utils::index_vec::IndexVec;
use inkwell as llvm;
use llvm::targets::TargetTriple;
use misc::{CodeModelWrapper, OptimisationLevelWrapper, RelocationModeWrapper};
use translation::Builder;

pub mod context;
pub mod misc;
pub mod translation;

// Re-export the context so that the `backend` can create it and
// pass it in.
pub use llvm::context::Context as LLVMContext;

pub struct ModuleData<'m> {
    /// The LLVM module.
    module: llvm::module::Module<'m>,

    /// The path to the file which contains the module.
    path: PathBuf,
}

impl<'b> ModuleData<'b> {
    /// Get a reference to the module that is associated with
    /// this [ModuleData].
    fn module(&self) -> &llvm::module::Module<'b> {
        &self.module
    }
}

pub struct LLVMBackend<'b, 'm> {
    /// The current compiler workspace, which is where the results of the
    /// linking and bytecode emission will be stored.
    workspace: &'b mut Workspace,

    /// The compiler settings associated with the current
    /// session.
    settings: &'b CompilerSettings,

    /// A map which maps a [ModuleId] to it's corresponding [ModuleData] and
    /// file paths.
    modules: FxHashMap<ModuleId, ModuleData<'m>>,

    /// The IR storage that is used to store the lowered IR, and all metadata
    /// about the IR.
    ir_storage: &'b IrStorage,

    /// All of the information about the layouts of types
    /// in the current session.
    layouts: &'b LayoutCtx,

    /// The target machine that we use to write all of the
    /// generated code into the object files.
    target_machine: llvm::targets::TargetMachine,
}

impl<'b, 'm> LLVMBackend<'b, 'm> {
    /// Create a new LLVM Backend from the given [BackendCtx].
    pub fn new(llvm_ctx: &'m LLVMContext, ctx: BackendCtx<'b>) -> Self {
        let BackendCtx { workspace, ir_storage, layout_storage: layouts, settings, .. } = ctx;

        // We have to create a target machine from the provided target
        // data.
        let target = settings.codegen_settings.target_info.target();

        // we have to initialise the target with the default configuration based
        // on which architecture we are compiling for.
        let config = llvm::targets::InitializationConfig::default();

        match target.arch {
            TargetArch::X86 | TargetArch::X86_64 => {
                llvm::targets::Target::initialize_x86(&config);
            }
            TargetArch::Arm => {
                llvm::targets::Target::initialize_arm(&config);
            }
            TargetArch::Aarch64 => {
                llvm::targets::Target::initialize_aarch64(&config);
            }
            TargetArch::Unknown => unreachable!(),
        }

        let llvm_target = llvm::targets::Target::from_name(target.arch.as_str()).unwrap();

        let target_triple = TargetTriple::create(target.name.as_ref());
        let target_machine = llvm_target
            .create_target_machine(
                &target_triple,
                target.cpu.as_ref(),
                target.cpu_features.as_ref(),
                OptimisationLevelWrapper::from(settings.optimisation_level).0,
                RelocationModeWrapper::from(target.relocation_mode).0,
                CodeModelWrapper::from(target.code_model).0,
            )
            .unwrap();

        let mut modules = FxHashMap::default();

        let entry_point = workspace.source_map.entry_point();
        modules.insert(
            entry_point,
            ModuleData {
                module: llvm_ctx.create_module(workspace.name.as_str()),
                path: workspace.module_bitcode_path(entry_point),
            },
        );

        Self { modules, workspace, target_machine, ir_storage, layouts, settings }
    }

    /// Verify all of the registered modules within the current
    /// backend instance. If a problem is found it causes the function
    /// to invoke a panic.
    fn verify_modules(&self) {
        for ModuleData { module, .. } in self.modules.values() {
            module.verify().unwrap();
        }
    }
}

impl<'b, 'm> Backend<'b> for LLVMBackend<'b, 'm> {
    /// This is the entry point for the LLVM backend, this is where each module
    /// is translated into an LLVM IR module and is then emitted as a bytecode
    /// module to the disk.
    fn run(&mut self) -> CompilerResult<()> {
        let entry_point = self.workspace.source_map.entry_point();
        let module = self.modules.get(&entry_point).unwrap().module();

        // @@Future: make it configurable whether we emit a module object per single
        // object, or if we emit a single module object for the entire program.
        // Currently, we are emitting a single module for the entire program
        // that is being compiled in in the workspace.
        let ctx = CodeGenCtx::new(module, self.settings, &self.ir_storage.ctx, self.layouts);

        // For each body perform a lowering procedure via the common interface...
        for body in self.ir_storage.bodies.iter() {
            // We don't need to generate anything for constants since they
            // should have already been dealt with...
            if matches!(body.info().source(), BodySource::Const) {
                continue;
            }

            // Get the instance of the function.

            let instance = self.ir_storage.ctx.map_ty(body.info().ty(), |ty| {
                let IrTy::Fn { instance, .. } = ty else {
                    panic!("ir-body has non-function type")
                };
                *instance
            });

            // @@ErrorHandling: we should be able to handle the error here
            codegen_ir_body::<Builder>(instance, body, &ctx).unwrap();
        }

        self.verify_modules();
        Ok(())
    }
}
