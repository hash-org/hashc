//! Hash Compiler VM crate.
#![feature(unchecked_math)]

use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::CompilerStageKind,
};
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

pub trait InterpreterCtx: CompilerInterface {}

impl<Ctx: InterpreterCtx> CompilerStage<Ctx> for Interpreter {
    fn run_stage(
        &mut self,
        _entry_point: SourceId,
        _ctx: &mut Ctx,
    ) -> hash_pipeline::interface::CompilerResult<()> {
        self.run().map_err(|err| vec![Report::from(err)])
    }

    fn stage_kind(&self) -> CompilerStageKind {
        CompilerStageKind::Full
    }
}
