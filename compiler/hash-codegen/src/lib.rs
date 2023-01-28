//! Hash compiler code generation crate. This crate contains interfaces for
//! a code generation stage to implement a translation stage between Hash IR
//! into some code representation for a backend to process. The current
//! available backends are the following:
//!
//! 1. The LLVM backend which translates Hash IR into LLVM IR so that it can be
//! compiled by LLVM into a native executable with the specified target
//! triple. The LLVM backend is located in the `hash-codegen-llvm` crate.
//!
//! 2. The bytecode backend which translates Hash IR into Hash Bytecode so that
//! it can be processed by the Hash VM. The bytecode backend is located in the
//! `hash-codegen-bytecode` crate.
//!
//! A backend that implements the `CodeGen` trait can be used to generate code
//! for a specific target, and then the compiler plumbing will continue after
//! the code is generated. Different backends may produce different "artifacts"
//! based on their requirements. For example, the VM backend will not emit any
//! artifacts since it will run the bytecode directly using the VM. On the other
//! hand, LLVM backend will emit a runnable executable after the code is
//! generated.
#![feature(let_chains, box_patterns, variant_count)]

pub mod common;
pub mod lower;
pub mod symbols;
pub mod traits;

// re-export `abi` and `layout` crates to make them available to the backend
// implementations.
pub use hash_abi as abi;
use hash_ir::IrStorage;
pub use hash_layout as layout;
use hash_pipeline::{settings::CompilerSettings, workspace::Workspace};

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
    pub settings: &'b CompilerSettings,

    /// Reference to the rayon thread pool.
    pub _pool: &'b rayon::ThreadPool,
}
