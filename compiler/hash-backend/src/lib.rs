//! Hash Compiler Backend driver. This deals with all of the
//! specifics of creating a code generation backend, interfacing
//! with the compiler pipeline, and generally orchestrating the
//! code generation process.
#![allow(dead_code)] // @@Temporary: until the codegen general purpose logic is completed.

use hash_ir::IrStorage;
use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::{CodeGenSettings, CompilerStageKind},
    workspace::Workspace,
    CompilerResult,
};
use hash_source::SourceId;

/// The Hash compiler code generator.
#[derive(Default)]
pub struct HashBackend;

impl HashBackend {
    /// Creates a new instance of the Hash backend.
    pub fn new() -> Self {
        Self
    }
}

/// The [BackendCtx] is the context that is needed for any [CodeGen]
/// backend to generate code for the target backend.
///
/// @@Todo: determine how we deal with "code store".
pub struct BackendCtx<'b> {
    /// Reference to the current compiler workspace.
    pub workspace: &'b mut Workspace,

    /// Reference to the IR storage that is used to store
    /// the lowered IR, and all metadata about the IR.
    pub ir_storage: &'b IrStorage,

    /// A reference to the backend settings in the current session.
    pub settings: &'b CodeGenSettings,

    /// Reference to the rayon thread pool.
    pub _pool: &'b rayon::ThreadPool,
}

pub trait BackendCtxQuery: CompilerInterface {
    fn data(&mut self) -> BackendCtx<'_>;
}

impl<Ctx: BackendCtxQuery> CompilerStage<Ctx> for HashBackend {
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::CodeGen
    }

    /// Setup the desired code generation backend. Deal with what IR bodies
    /// need to be lowered and how via the `hash-codegen` interfaces, then
    /// deal with the specifics of the backend (i.e. does it need to link
    /// the module, does it need to emit an archive, etc).
    ///
    /// @@Todo: introduce a `CodeStore` trait that can be used to store.
    ///
    /// @@Todo: deal with code generation settings in order to pick the
    /// correct backend in order to generate code.
    ///
    /// @@Future: think about how we can deal with multiple backends at the
    /// same time for the purpose of compile-time evaluation of code. This
    /// evaluation should occur in a separate thread, we a separate VM for
    /// running the specified code.
    fn run(&mut self, _: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let BackendCtx { .. } = ctx.data();
        Ok(())
    }
}
