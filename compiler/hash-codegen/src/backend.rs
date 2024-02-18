//! This module defines the [CompilerBackend] trait which is
//! used to represent a compiler backend that the pipeline can
//! interface with. The trait is simple and only requires for
//! the backend to implement the [CompilerBackend::run] method
//! which is called by the pipeline to generate code for the
//! processed [Workspace].

use hash_ir::IrStorage;
use hash_pipeline::{
    interface::{CompilerOutputStream, CompilerResult},
    settings::CompilerSettings,
    workspace::Workspace,
};
use hash_repr::LayoutStorage;
use hash_utils::rayon;

use crate::traits::abi::FnAbiStore;

/// The [CodeGenStorage] stores useful created information
/// during code generation. Currently, it is used to store
/// a map between function instances and their associated
/// ABIs.
#[derive(Default)]
pub struct CodeGenStorage {
    /// The function ABIs that have been created.
    fn_abi_store: FnAbiStore,
}

impl CodeGenStorage {
    /// Create a new [CodeGenStorage].
    pub fn new() -> Self {
        Self::default()
    }

    /// Get a reference to the function ABI store.
    pub fn abis(&self) -> &FnAbiStore {
        &self.fn_abi_store
    }
}

/// The [BackendCtx] is the context that is needed for any
/// [CompilerBackend] to generate code for the target backend.
pub struct BackendCtx<'b> {
    /// Reference to the current compiler workspace.
    pub workspace: &'b mut Workspace,

    /// Reference to the codegen storage that is used to store information
    /// about the generated code, and accompanying metadata.
    pub codegen_storage: &'b CodeGenStorage,

    /// Reference to the IR storage that is used to store
    /// the lowered IR, and all metadata about the IR.
    pub icx: &'b IrStorage,

    /// All of the layout information about the types in the
    /// current session.
    pub lcx: &'b LayoutStorage,

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

/// The [CompilerBackend] trait specifies the required interface that needs
/// to be implemented by a backend in order to interface with the
/// pipeline.
pub trait CompilerBackend<'b> {
    /// The [`CompilerBackend::run`] method is called by the pipeline to
    /// generate code for the specified source file. This method
    /// may return a potential error which implies that something
    /// went wrong during the code generation process, and it should
    /// be treated as a fatal error.
    ///
    /// When the run is complete, all of the "bit-code" modules that
    /// will have been generated will be applied to the [Workspace].
    fn run(&mut self) -> CompilerResult<()>;
}
