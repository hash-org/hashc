//! Hash Compiler Backend driver. This deals with all of the
//! specifics of creating a code generation backend, interfacing
//! with the compiler pipeline, and generally orchestrating the
//! code generation process.

use hash_codegen::backend::{Backend, BackendCtx};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::{CodeGenBackend, CompilerStageKind},
    CompilerResult,
};
use hash_source::SourceId;

/// The Hash compiler code generator.
#[derive(Default)]
pub struct CodeGenPass;

impl CodeGenPass {
    /// Creates a new instance of the Hash backend.
    pub fn new() -> Self {
        Self
    }
}

pub trait BackendCtxQuery: CompilerInterface {
    fn data(&mut self) -> BackendCtx<'_>;
}

impl<Ctx: BackendCtxQuery> CompilerStage<Ctx> for CodeGenPass {
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::CodeGen
    }

    /// Setup the desired code generation backend. Deal with what IR bodies
    /// need to be lowered and how via the `hash-codegen` interfaces, then
    /// deal with the specifics of the backend (i.e. does it need to link
    /// the module, does it need to emit an archive, etc).
    ///
    /// @@Future: think about how we can deal with multiple backends at the
    /// same time for the purpose of compile-time evaluation of code. This
    /// evaluation should occur in a separate thread, we a separate VM for
    /// running the specified code.
    fn run(&mut self, _: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let BackendCtx { settings, .. } = ctx.data();

        // Create a new instance of a backend, and then add each bo
        let mut backend = match settings.codegen_settings.backend {
            CodeGenBackend::LLVM => create_llvm_backend(ctx.data()),
            CodeGenBackend::VM => unimplemented!(),
        };

        backend.run()
    }
}

pub fn create_llvm_backend<'b>(ctx: BackendCtx<'b>) -> Box<dyn Backend<'b> + 'b> {
    Box::new(hash_codegen_llvm::LLVMBackend::new(ctx))
}
