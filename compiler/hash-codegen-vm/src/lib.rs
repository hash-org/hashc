//! Hash compiler bytecode code generation crate. This crate contains
//! all of the logic of transforming generated Hash IR into Hash Bytecode
//! so that it can be processed by the Hash VM.

mod ctx;
mod translation;

use hash_attrs::builtin::attrs;
use hash_codegen::{
    backend::{BackendCtx, CodeGenStorage, CompilerBackend},
    lower::codegen_body,
    repr::LayoutStorage,
};
use hash_ir::{IrStorage, ir, ty::InstanceHelpers};
use hash_pipeline::{interface::CompilerResult, settings::CompilerSettings, workspace::Workspace};
use hash_source::SourceMapUtils;
use hash_storage::store::statics::StoreId;
use hash_utils::profiling::{HasMutMetrics, StageMetrics};
use hash_vm::builder::FunctionBuilder;

use crate::{ctx::Ctx, translation::VMBuilder};

pub struct VMBackend<'b> {
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

    /// All of the metrics that are collected when running the LLVM
    /// backend. This contains a map of `stages` to the time it took
    /// to run the stage.
    metrics: &'b mut StageMetrics,
}

impl HasMutMetrics for VMBackend<'_> {
    fn metrics(&mut self) -> &mut StageMetrics {
        self.metrics
    }
}

impl<'b> VMBackend<'b> {
    /// Create a new LLVM Backend from the given [BackendCtx].
    pub fn new(ctx: BackendCtx<'b>, metrics: &'b mut StageMetrics) -> Self {
        let BackendCtx {
            workspace, icx: ir_storage, codegen_storage, lcx: layouts, settings, ..
        } = ctx;

        Self { settings, workspace, ir_storage, codegen_storage, layouts, metrics }
    }

    fn build_bodies(&self, ctx: &Ctx) {
        let ir = self.ir_storage;

        // For each body perform a lowering procedure via the common interface...
        for body in ir.bodies.iter() {
            // We don't need to generate anything for constants since they
            // should have already been dealt with...
            if matches!(body.metadata().source(), ir::BodySource::Const) {
                continue;
            }

            // Create a new `FunctionBuilder` and register it to the given
            // instance.
            let instance = body.metadata().ty().borrow().as_instance();
            let fn_builder = FunctionBuilder::new(instance);
            ctx.builder.new_function(fn_builder);

            // @@ErrorHandling: we should be able to handle the error here
            codegen_body::<VMBuilder>(instance, body, ctx).unwrap();

            if instance.borrow().has_attr(attrs::DUMP_BYTECODE) {
                // @@Messaging
                log::info!(
                    "LLVM IR for function {}\n{}",
                    body.meta.name(),
                    "<dumped bytecode here>"
                );
            }
        }
    }

    fn optimise(&self, _ctx: &Ctx) {
        // @@BytecodeOpt: implement bytecode optimisations here...
    }
}

impl<'b> CompilerBackend<'b> for VMBackend<'b> {
    fn run(&mut self) -> CompilerResult<()> {
        let _ = SourceMapUtils::entry_point().expect("expected a defined entry point");
        let module_name = self.workspace.name.clone();

        let ctx = Ctx::new(self.settings, &self.ir_storage.ctx, self.codegen_storage, self.layouts);

        self.record("build", |this| this.build_bodies(&ctx));

        // If the settings specify that the bytecode should be emitted, then
        // we write the emitted bytecode to standard output.
        if self.settings.codegen_settings.dump_bytecode {
            log::info!("Bytecode dump for module `{module_name}`:\n{}", "<dumped bytecode here>",);
        }

        self.record("optimise", |this| this.optimise(&ctx));
        Ok(())
    }
}
