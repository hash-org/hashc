//! The LLVM code generation backend for Hash. This implements the [Backend]
//! trait that provides an interface between a code generation backend and the
//! actual compiler pipeline, the [BackendCtx] trait which provides an interface
//! between the backend and the compiler context, and the [LLVMBackend] struct
//! which is the actual implementation of the LLVM backend. It is expected that
//! the backend performs it's work in the [LLVMBackend::run] method, and saves
//! the results of each module in the [Workspace].
#![feature(let_chains, hash_raw_entry)]
#![allow(unused)]

use std::path::PathBuf;

use context::CodeGenCtx;
use hash_codegen::{
    backend::{Backend, BackendCtx},
    layout::LayoutCtx,
};
use hash_ir::IrStorage;
use hash_pipeline::{settings::CompilerSettings, workspace::Workspace, CompilerResult};
use hash_source::ModuleId;
use hash_target::TargetArch;
use hash_utils::index_vec::IndexVec;
use inkwell as llvm;
use llvm::targets::TargetTriple;
use misc::{CodeModelWrapper, OptimisationLevelWrapper, RelocationModeWrapper};

pub mod context;
pub mod misc;
pub mod translation;

pub struct ModuleData<'b> {
    /// The LLVM module.
    module: llvm::module::Module<'b>,

    /// The path to the file which contains the module.
    path: PathBuf,
}

pub struct LLVMBackend<'b> {
    /// The current compiler workspace, which is where the results of the
    /// linking and bytecode emission will be stored.
    workspace: &'b mut Workspace,

    /// The compiler settings associated with the current
    /// session.
    settings: &'b CompilerSettings,

    /// A map which maps a [ModuleId] to it's corresponding [llvm::Module] and
    /// file paths.
    modules: IndexVec<ModuleId, ModuleData<'b>>,

    /// The IR storage that is used to store the lowered IR, and all metadata
    /// about the IR.
    ir_storage: &'b IrStorage,

    /// All of the information about the layouts of types
    /// in the current session.
    layouts: &'b LayoutCtx,

    /// The LLVM context.
    context: llvm::context::Context,

    /// The target machine that we use to write all of the
    /// generated code into the object files.
    target_machine: llvm::targets::TargetMachine,
}

impl<'b> LLVMBackend<'b> {
    /// Create a new LLVM Backend from the given [BackendCtx].
    pub fn new(ctx: BackendCtx<'b>) -> Self {
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

        let context = llvm::context::Context::create();

        Self {
            modules: IndexVec::new(),
            workspace,
            context,
            target_machine,
            ir_storage,
            layouts,
            settings,
        }
    }
}

impl<'b> Backend<'b> for LLVMBackend<'b> {
    /// This is the entry point for the LLVM backend, this is where each module
    /// is translated into an LLVM IR module and is then emitted as a bytecode
    /// module to the disk.
    fn run(&mut self) -> CompilerResult<()> {
        // @@Future: make it configurable whether we emit a module object per single
        // object, or if we emit a single module object for the entire program.
        // Currently, we are emitting a single module for the entire program
        // that is being compiled in in the workspace.
        let module = self.context.create_module(self.workspace.name.as_str());

        let ctx = CodeGenCtx::new(module, self.settings, &self.ir_storage.ctx, self.layouts);

        Ok(())
    }
}
