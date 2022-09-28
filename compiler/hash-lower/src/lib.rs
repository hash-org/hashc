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
use hash_pipeline::traits::{Lowering, CompilerResult};
use hash_source::{
    location::{SourceLocation, Span},
    SourceId,
};

use self::builder::Builder;

/// The [IrLowerer] is used as a bootstrapping mechanism to kick off the
/// [Builder] working on functions that it discovers as the the lower traverses
/// through the source files.
pub struct IrLowerer;

pub struct IrLoweringState<'ir> {
    interactive_body: Body<'ir>,
}

impl<'ir> Default for IrLoweringState<'ir> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'ir> IrLoweringState<'ir> {
    pub fn new() -> Self {
        let dummy_span = SourceLocation::new(Span::default(), SourceId::default());

        Self { interactive_body: Body::new_uninitialised(dummy_span) }
    }
}

impl Lowering for IrLowerer {
    fn lower_interactive_block(
        &mut self,
        _interactive_id: hash_source::InteractiveId,
        _workspace: &hash_pipeline::sources::Workspace,
    ) -> CompilerResult<()> {
        Ok(())
    }

    fn lower_module(
        &mut self,
        _module_id: hash_source::ModuleId,
        _workspace: &hash_pipeline::sources::Workspace,
    ) -> CompilerResult<()> {
        // We need to iterate all of the modules and essentially perform
        // a discovery process for what needs to be lowered...

        Ok(())
    }
}
