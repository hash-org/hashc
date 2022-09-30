//! Hash Compiler VM crate.
#![feature(unchecked_math)]

use hash_pipeline::{settings::CompilerStageKind, sources::Workspace, traits::CompilerStage};
use hash_reporting::report::Report;
use hash_source::SourceId;
use vm::Interpreter;

mod heap;
mod stack;

pub mod bytecode;
pub mod register;

pub mod bytecode_builder;
pub mod error;
pub mod vm;

impl CompilerStage for Interpreter {
    fn run_stage(
        &mut self,
        _entry_point: SourceId,
        _workspace: &mut Workspace,
        _pool: &rayon::ThreadPool,
    ) -> hash_pipeline::traits::CompilerResult<()> {
        self.run().map_err(|err| vec![Report::from(err)])
    }

    fn stage_kind(&self) -> CompilerStageKind {
        CompilerStageKind::Full
    }
}
