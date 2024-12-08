//! Hash compiler bytecode code generation crate. This crate contains
//! all of the logic of transforming generated Hash IR into Hash Bytecode
//! so that it can be processed by the Hash VM.
#![allow(unused)]

use hash_codegen::{
    backend::{BackendCtx, CodeGenStorage, CompilerBackend},
    repr::LayoutStorage,
};
use hash_ir::IrStorage;
use hash_pipeline::{interface::CompilerResult, settings::CompilerSettings, workspace::Workspace};
use hash_utils::{
    profiling::{HasMutMetrics, StageMetrics},
    stream::CompilerOutputStream,
};

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
}

impl<'b> CompilerBackend<'b> for VMBackend<'b> {
    fn run(&mut self) -> CompilerResult<()> {
        todo!()
    }
}
