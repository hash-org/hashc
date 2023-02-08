//! The LLVM code generation backend for Hash. This implements the [Backend]
//! trait that provides an interface between a code generation backend and the
//! actual compiler pipeline, the [BackendCtx] trait which provides an interface
//! between the backend and the compiler context, and the [LLVMBackend] struct
//! which is the actual implementation of the LLVM backend. It is expected that
//! the backend performs it's work in the [LLVMBackend::run] method, and saves
//! the results of each module in the [Workspace].
#![feature(let_chains, hash_raw_entry)]

use context::CodeGenCtx;
use hash_codegen::{
    backend::{BackendCtx, CompilerBackend},
    layout::LayoutCtx,
    lower::{abi::compute_fn_abi_from_instance, codegen_ir_body},
    symbols::mangle::compute_symbol_name,
    traits::{
        builder::BlockBuilderMethods, constants::ConstValueBuilderMethods,
        misc::MiscBuilderMethods, ty::TypeBuilderMethods,
    },
};
use hash_ir::{ir::BodySource, ty::IrTy, IrStorage};
use hash_pipeline::{
    interface::CompilerOutputStream, settings::CompilerSettings, workspace::Workspace,
    CompilerResult,
};
use hash_reporting::reporter::Reporter;
use hash_source::ModuleId;
use hash_target::TargetArch;
use hash_utils::stream_writeln;
use inkwell as llvm;
use llvm::{
    passes::{PassManager, PassManagerBuilder},
    targets::{FileType, TargetTriple},
    values::FunctionValue,
};
use misc::{CodeModelWrapper, OptimisationLevelWrapper, RelocationModeWrapper};
use translation::Builder;

pub mod context;
pub mod misc;
pub mod translation;

// Re-export the context so that the `backend` can create it and
// pass it in.
pub use llvm::{context::Context as LLVMContext, module::Module as LLVMModule};

pub struct LLVMBackend<'b> {
    /// The stream to use for printing out the results
    /// of the lowering operation.
    stdout: CompilerOutputStream,

    /// The current compiler workspace, which is where the results of the
    /// linking and bytecode emission will be stored.
    workspace: &'b mut Workspace,

    /// The compiler settings associated with the current
    /// session.
    settings: &'b CompilerSettings,

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

impl<'b> LLVMBackend<'b> {
    /// Create a new LLVM Backend from the given [BackendCtx].
    pub fn new(ctx: BackendCtx<'b>) -> Self {
        let BackendCtx { workspace, ir_storage, layout_storage: layouts, settings, stdout, .. } =
            ctx;

        // We have to create a target machine from the provided target
        // data.
        let target = settings.target();

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

        Self { workspace, target_machine, ir_storage, layouts, settings, stdout }
    }

    fn optimise(&self, module: &LLVMModule) -> CompilerResult<()> {
        let pass_manager_builder = PassManagerBuilder::create();

        let OptimisationLevelWrapper(opt_level) = self.settings.optimisation_level.into();
        pass_manager_builder.set_optimization_level(opt_level);

        let size_opt_level = self.settings.optimisation_level.size_level();
        pass_manager_builder.set_size_level(size_opt_level as u32);

        // Now run the optimisations on the given module.
        let pass_manager = PassManager::create(());
        pass_manager_builder.populate_module_pass_manager(&pass_manager);
        pass_manager.run_on(module);

        Ok(())
    }

    /// Write the given [LLVMModule] to the disk, whilst also ensuring that it
    /// is valid before the module.
    fn write_module(&self, module: &LLVMModule, id: ModuleId) -> CompilerResult<()> {
        module.verify().map_err(|err| {
            let mut builder = Reporter::new();
            let report = builder.internal().title("LLVM Module verification Error");

            for line in err.to_string().lines() {
                report.add_info(line);
            }

            builder.into_reports()
        })?;

        // For now, we assume that the object file extension is always `.o`.
        let path = self.workspace.module_bitcode_path(id, "o");

        // Check if we need to create the "build" folder
        if let Some(parent) = path.parent() && !parent.exists() {
            std::fs::create_dir_all(parent).unwrap();
        }

        self.target_machine.write_to_file(module, FileType::Object, &path).unwrap();
        Ok(())
    }

    /// Function that defines a function wrapper for the "main" entry
    /// point of the program, this generates some boiler plate code to
    /// deal with the commandline arguments being passed in, and the
    /// sets some additional attributes on the function. Then, a call
    /// is generated tot the actual entry point of the program.
    fn define_entry_point<'m>(
        &self,
        ctx: &CodeGenCtx<'b, 'm>,
    ) -> CompilerResult<FunctionValue<'m>> {
        // If the target requires that the arguments are passed in
        // through the arguments of the function, i.e. `int main(int argc, char** argv)`
        // then we have to define it as such, otherwise, we define it as
        // `int main()`.
        let fn_ty = if self.settings.target().entry_point_requires_args {
            ctx.type_function(&[ctx.type_int(), ctx.type_ptr_to(ctx.type_i8p())], ctx.type_int())
        } else {
            ctx.type_function(&[], ctx.type_int())
        };

        // Declare the main function
        let Some(main_fn) = ctx.declare_entry_point(fn_ty) else {
            unreachable!("main function already declared")
        };

        // @@Todo: we can set additional attributes to this, i.e. cpu_attrs

        let block = Builder::append_block(ctx, main_fn, "init");
        let mut builder = Builder::build(ctx, block);

        // Get the instance of the entry point function so that
        // we can reference it here.
        let entry_point = self.ir_storage.entry_point.def().unwrap();
        let user_main = ctx.get_fn(entry_point);

        builder.call(user_main, &[], None);

        // @@Todo: the wrapper should return an exit code value?
        // let cast = builder.int_cast(result, ctx.type_int(), false);
        builder.return_value(builder.const_i32(0));

        Ok(main_fn)
    }
}

impl<'b> CompilerBackend<'b> for LLVMBackend<'b> {
    /// This is the entry point for the LLVM backend, this is where each module
    /// is translated into an LLVM IR module and is then emitted as a bytecode
    /// module to the disk.
    fn run(&mut self) -> CompilerResult<()> {
        // @@Future: make it configurable whether we emit a module object per single
        // object, or if we emit a single module object for the entire program.
        // Currently, we are emitting a single module for the entire program
        // that is being compiled in in the workspace.
        let entry_point = self.workspace.source_map.entry_point().unwrap();

        let context = LLVMContext::create();

        let module_name = self.workspace.name.as_str();
        let module = context.create_module(module_name);
        let ctx = CodeGenCtx::new(&module, self.settings, &self.ir_storage.ctx, self.layouts);

        // We perform an initial pass where we pre-define everything so that
        // we can get place all of the symbols in the symbol table first.
        for body in self.ir_storage.bodies.iter() {
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

            // So, we create the mangled symbol name, and then call `predefine()` which
            // should create the function ABI from the instance, with the correct
            // attributes and linkage, etc.
            let symbol_name = compute_symbol_name(&self.ir_storage.ctx, instance);

            let abi = compute_fn_abi_from_instance(&ctx, instance).unwrap();
            ctx.predefine_fn(instance, symbol_name.as_str(), &abi);
        }

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

        // Now we define the entry point of the function, if there is one
        if self.ir_storage.entry_point.has() {
            self.define_entry_point(&ctx)?;
        }

        // If the settings specify that the bytecode should be emitted, then
        // we write the emitted bytecode to standard output.
        if self.settings.codegen_settings.dump {
            let stdout = &mut self.stdout;
            stream_writeln!(
                stdout,
                "LLVM IR dump for module `{module_name}`:\n{}",
                module.print_to_string().to_string()
            );
        }

        self.optimise(&module)?;
        self.write_module(&module, entry_point)
    }
}
