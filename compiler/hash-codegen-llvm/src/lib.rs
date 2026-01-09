//! The LLVM code generation backend for Hash. This implements the [Backend]
//! trait that provides an interface between a code generation backend and the
//! actual compiler pipeline, the [BackendCtx] trait which provides an interface
//! between the backend and the compiler context, and the [LLVMBackend] struct
//! which is the actual implementation of the LLVM backend. It is expected that
//! the backend performs it's work in the [LLVMBackend::run] method, and saves
//! the results of each module in the [Workspace].

mod ctx;
mod error;
pub mod misc;
mod translation;

use ctx::CodeGenCtx;
use error::{CodeGenError, CodegenResult};
use hash_attrs::builtin::attrs;
use hash_codegen::{
    backend::{BackendCtx, CodeGenStorage, CompilerBackend},
    lower::codegen_body,
    repr::LayoutStorage,
    symbols::mangle::compute_symbol_name,
    target::{HasTarget, TargetArch},
    traits::{
        builder::BlockBuilderMethods, constants::ConstValueBuilderMethods,
        misc::MiscBuilderMethods, ty::TypeBuilderMethods,
    },
};
use hash_ir::{IrStorage, ir::BodySource, ty::InstanceHelpers};
use hash_pipeline::{
    interface::{CompilerResult, StageMetrics},
    settings::CompilerSettings,
    workspace::Workspace,
};
use hash_source::{ModuleId, SourceMapUtils};
use hash_storage::store::{Store, statics::StoreId};
use hash_utils::{log, profiling::HasMutMetrics};
use inkwell as llvm;
use llvm::{
    context::Context as LLVMContext,
    module::Module as LLVMModule,
    passes::PassManager,
    targets::{FileType, TargetTriple},
    types::AnyType,
    values::{AnyValue, FunctionValue},
};
use misc::{CodeModelWrapper, OptimisationLevelWrapper, RelocationModeWrapper};
use translation::LLVMBuilder;

pub struct LLVMBackend<'b> {
    /// The current compiler workspace, which is where the results of the
    /// linking and bytecode emission will be stored.
    workspace: &'b mut Workspace,

    /// The compiler settings associated with the current
    /// session.
    settings: &'b CompilerSettings,

    /// The IR storage that is used to store the lowered IR, and all metadata
    /// about the IR.
    ir_storage: &'b IrStorage,

    /// The codegen storage, stores information about objects that were
    /// generated during code generation.
    codegen_storage: &'b CodeGenStorage,

    /// All of the information about the layouts of types
    /// in the current session.
    layouts: &'b LayoutStorage,

    /// The target machine that we use to write all of the
    /// generated code into the object files.
    target_machine: llvm::targets::TargetMachine,

    /// All of the metrics that are collected when running the LLVM
    /// backend. This contains a map of `stages` to the time it took
    /// to run the stage.
    metrics: &'b mut StageMetrics,
}

impl HasMutMetrics for LLVMBackend<'_> {
    fn metrics(&mut self) -> &mut StageMetrics {
        self.metrics
    }
}

impl<'b, 'm> LLVMBackend<'b> {
    /// Create a new LLVM Backend from the given [BackendCtx].
    pub fn new(ctx: BackendCtx<'b>, metrics: &'b mut StageMetrics) -> Self {
        let BackendCtx {
            workspace, icx: ir_storage, codegen_storage, lcx: layouts, settings, ..
        } = ctx;

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

        Self { workspace, target_machine, ir_storage, codegen_storage, layouts, settings, metrics }
    }

    /// Create an [PassManager] for LLVM, apply the optimisation options and run
    /// the optimised on the given [LLVMModule].
    fn optimise(&self, module: &LLVMModule) -> CompilerResult<()> {
        let pass_manager = PassManager::create(());
        pass_manager.run_on(module);

        Ok(())
    }

    /// Write the given [LLVMModule] to the disk, whilst also ensuring that it
    /// is valid before the module.
    fn write_module(&mut self, module: &LLVMModule, id: ModuleId) -> CodegenResult<()> {
        // If verification fails, this is a bug on our side, and we emit an
        // internal error.
        module.verify().map_err(|err| CodeGenError::ModuleVerificationFailed { reason: err })?;

        // For now, we assume that the object file extension is always `.o`.
        let path = self.workspace.module_bitcode_path(id, "o");

        // Check if we need to create the "build" folder
        if let Some(parent) = path.parent()
            && !parent.exists()
        {
            std::fs::create_dir_all(parent).unwrap();
        }

        // If the `-Cemit=asm` flag was specified then we will also emit the
        // assembly code for the module.
        if self.settings.codegen_settings.dump_assembly {
            let asm_path = self.workspace.module_bitcode_path(id, "s");
            self.target_machine
                .write_to_file(module, FileType::Assembly, &asm_path)
                .map_err(|err| CodeGenError::ModuleWriteFailed { reason: err })?;

            // @@Messaging
            log::info!("wrote assembly file to `{}`", asm_path.to_string_lossy());
        }

        self.target_machine
            .write_to_file(module, FileType::Object, &path)
            .map_err(|err| CodeGenError::ModuleWriteFailed { reason: err })?;
        self.workspace.code_map.add_object_file(id, path);
        Ok(())
    }

    /// Function that defines a function wrapper for the "main" entry
    /// point of the program, this generates some boiler plate code to
    /// deal with the commandline arguments being passed in, and the
    /// sets some additional attributes on the function. Then, a call
    /// is generated tot the actual entry point of the program.
    fn define_entry_point(&self, ctx: &CodeGenCtx<'b, 'm>) -> CompilerResult<FunctionValue<'m>> {
        // If the target requires that the arguments are passed in
        // through the arguments of the function, i.e. `int main(int argc, char** argv)`
        // then we have to define it as such, otherwise, we define it as
        // `int main()`.
        let fn_ty = if ctx.target().entry_point_requires_args {
            ctx.type_function(&[ctx.type_int(), ctx.type_ptr()], ctx.type_int())
        } else {
            ctx.type_function(&[], ctx.type_int())
        };

        // Declare the main function
        let Some(main_fn) = ctx.declare_entry_point(fn_ty) else {
            unreachable!("main function already declared")
        };

        // @@Todo: we can set additional attributes to this, i.e. cpu_attrs

        let block = LLVMBuilder::append_block(ctx, main_fn, "init");
        let mut builder = LLVMBuilder::build(ctx, block);

        // Get the instance of the entry point function so that
        // we can reference it here.
        let entry_point = self.ir_storage.entry_point.def().unwrap();
        let user_main = ctx.get_fn(entry_point);
        let fn_ty = user_main.get_type().as_any_type_enum();

        builder.call(fn_ty, user_main.as_any_value_enum(), &[], None);

        // @@Todo: the wrapper should return an exit code value?
        // let cast = builder.int_cast(result, ctx.type_int(), false);
        builder.return_value(builder.const_i32(0));

        Ok(main_fn)
    }

    fn predefine_bodies(&self, ctx: &CodeGenCtx<'b, 'm>) {
        // We perform an initial pass where we pre-define everything so that
        // we can get place all of the symbols in the symbol table first.
        for body in self.ir_storage.bodies.iter() {
            if matches!(body.metadata().source(), BodySource::Const) {
                continue;
            }

            // Get the instance of the function.
            let ty = body.metadata().ty();
            let instance = ty.borrow().as_instance();

            // So, we create the mangled symbol name, and then call `predefine()` which
            // should create the function ABI from the instance, with the correct
            // attributes and linkage, etc.
            let symbol_name = compute_symbol_name(instance);

            let abis = self.codegen_storage.abis();
            let abi = abis.create_fn_abi_from_ty(ctx, ty);

            abis.map_fast(abi, |abi| {
                ctx.predefine_fn(instance, symbol_name.as_str(), abi);
            });
        }
    }

    /// This function will build each body that is stored in the IR, and it to
    /// the current module.
    fn build_bodies(&self, ctx: &CodeGenCtx<'b, 'm>) {
        let ir = self.ir_storage;

        // For each body perform a lowering procedure via the common interface...
        for body in ir.bodies.iter() {
            // We don't need to generate anything for constants since they
            // should have already been dealt with...
            if matches!(body.metadata().source(), BodySource::Const) {
                continue;
            }

            // @@ErrorHandling: we should be able to handle the error here
            codegen_body::<LLVMBuilder>(body, ctx).unwrap();

            // Check if we should dump the generated LLVM IR
            let instance = body.metadata().ty().borrow().as_instance();
            if instance.borrow().has_attr(attrs::DUMP_LLVM_IR) {
                // @@Messaging
                log::info!(
                    "LLVM IR for function {}\n{}",
                    body.meta.name(),
                    ctx.get_fn(instance).print_to_string().to_string()
                );
            }
        }
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
        let entry_point =
            SourceMapUtils::entry_point().expect("expected a defined entry point for executable");

        let context = LLVMContext::create();

        let module_name = self.workspace.name.clone();
        let module = context.create_module(module_name.as_str());

        module.set_source_file_name(&module_name);
        module.set_triple(&self.target_machine.get_triple());
        module.set_data_layout(&self.target_machine.get_target_data().get_data_layout());

        let ctx = CodeGenCtx::new(
            &module,
            self.settings,
            &self.ir_storage.ctx,
            self.layouts,
            self.codegen_storage,
        );

        self.record("predefine", |this| this.predefine_bodies(&ctx));
        self.record("build", |this| this.build_bodies(&ctx));

        // Now we define the entry point of the function, if there is one
        if self.ir_storage.entry_point.has() {
            self.define_entry_point(&ctx)?;
        }

        // If the settings specify that the bytecode should be emitted, then
        // we write the emitted bytecode to standard output.
        if self.settings.codegen_settings.dump_bytecode {
            log::info!(
                "LLVM IR dump for module `{module_name}`:\n{}",
                module.print_to_string().to_string()
            );
        }

        self.record("optimise", |this| this.optimise(&module))?;
        self.record("write", |this| {
            this.write_module(&module, entry_point.into()).map_err(|err| vec![err.into()])
        })
    }
}
