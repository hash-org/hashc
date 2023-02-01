//! This module defines all of the useful traits and data types that
//! are used by the code generation backend to interface with
//! the compiler pipeline.

use hash_ir::IrStorage;
use hash_layout::LayoutCtx;
use hash_pipeline::{
    interface::CompilerOutputStream, settings::CompilerSettings, workspace::Workspace,
    CompilerResult,
};

/// The [BackendCtx] is the context that is needed for any
/// [Backend] to generate code for the target backend.
pub struct BackendCtx<'b> {
    /// Reference to the current compiler workspace.
    pub workspace: &'b mut Workspace,

    /// Reference to the IR storage that is used to store
    /// the lowered IR, and all metadata about the IR.
    pub ir_storage: &'b IrStorage,

    /// All of the layout information about the types in the
    /// current session.
    pub layout_storage: &'b LayoutCtx,

    /// A reference to the backend settings in the current session.
    pub settings: &'b CompilerSettings,

    /// Reference to the output stream
    pub stdout: CompilerOutputStream,

    /// Reference to the rayon thread pool.
    ///
    /// @@Future: hopefully use this so that we can maximise the number of code
    /// gen units for each module?
    pub _pool: &'b rayon::ThreadPool,
}

/// The [Backend] trait specifies the required interface that needs
/// to be implemented by a backend in order to interface with the
/// pipeline.
pub trait Backend<'b> {
    /// The [Backend::run] method is called by the pipeline to
    /// generate code for the specified source file. This method
    /// may return a potential error which implies that something
    /// went wrong during the code generation process, and it should
    /// be treated as a fatal error.
    ///
    /// When the run is complete, all of the "bit-code" modules that
    /// will have been generated will be applied to the [Workspace].
    fn run(&mut self) -> CompilerResult<()>;
}
