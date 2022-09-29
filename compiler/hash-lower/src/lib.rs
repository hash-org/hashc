//! Hash Intermediate Representation builder. This crate contains the
//! functionality that converts the Hash typed AST into Hash IR. Additionally,
//! the Hash IR builder crate contains implemented passes that will optimise the
//! IR, performing optimisations such as constant folding or dead code
//! elimination.
#![allow(unused)] // @@TODO: remove this when the builder is complete

pub mod builder;
mod cfg;
mod visitor;

use hash_ir::ir::Body;
use hash_pipeline::{
    settings::CompilerStageKind,
    traits::{CompilerResult, CompilerStage},
};
use hash_source::{
    location::{SourceLocation, Span},
    SourceId,
};

use self::builder::Builder;

/// The [IrLowerer] is used as a bootstrapping mechanism to kick off the
/// [Builder] working on functions that it discovers as the the lower traverses
/// through the source files.
pub struct IrLowerer;

impl<'pool> CompilerStage<'pool> for IrLowerer {
    fn stage_kind(&self) -> CompilerStageKind {
        CompilerStageKind::IrGen
    }

    fn run_stage(
        &mut self,
        entry_point: SourceId,
        workspace: &mut hash_pipeline::sources::Workspace,
        pool: &'pool rayon::ThreadPool,
    ) -> CompilerResult<()> {
        // We need to iterate all of the modules and essentially perform
        // a discovery process for what needs to be lowered...

        Ok(())
    }
}
