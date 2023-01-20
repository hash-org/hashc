//! Hash Compiler Backend driver. This deals with all of the
//! specifics of creating a code generation backend, interfacing
//! with the compiler pipeline, and generally orchestrating the
//! code generation process.
#![allow(dead_code)] // @@Temporary: until the codegen general purpose logic is completed.

use hash_codegen::BackendCtx;
use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::CompilerStageKind,
    CompilerResult,
};
use hash_source::SourceId;

/// The Hash compiler code generator.
#[derive(Default)]
pub struct Backend;

impl Backend {
    /// Creates a new instance of the Hash backend.
    pub fn new() -> Self {
        Self
    }
}

pub trait BackendCtxQuery: CompilerInterface {
    fn data(&mut self) -> BackendCtx<'_>;
}

impl<Ctx: BackendCtxQuery> CompilerStage<Ctx> for Backend {
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
