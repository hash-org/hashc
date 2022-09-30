//! Hash Intermediate Representation builder. This crate contains the
//! functionality that converts the Hash typed AST into Hash IR. Additionally,
//! the Hash IR builder crate contains implemented passes that will optimise the
//! IR, performing optimisations such as constant folding or dead code
//! elimination.
#![allow(unused)] // @@TODO: remove this when the builder is complete

pub mod builder;
mod cfg;
mod visitor;

use hash_ast::ast::{AstNodeRef, Expr, OwnsAstNode};
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
pub struct IrLowerer {
    //<'ir> {
    // items_to_lower: Vec<AstNodeRef<'ir, Expr>>
}

impl IrLowerer {
    pub fn new() -> Self {
        Self {
            // items_to_lower: vec![]
        }
    }
}

impl Default for IrLowerer {
    fn default() -> Self {
        Self::new()
    }
}

impl CompilerStage for IrLowerer {
    fn stage_kind(&self) -> CompilerStageKind {
        CompilerStageKind::IrGen
    }

    fn run_stage(
        &mut self,
        entry_point: SourceId,
        workspace: &mut hash_pipeline::sources::Workspace,
        pool: &rayon::ThreadPool,
    ) -> CompilerResult<()> {
        // We need to iterate all of the modules and essentially perform
        // a discovery process for what needs to be lowered...

        if let SourceId::Module(id) = entry_point {
            let module = workspace.node_map.get_module(id);

            for expr in module.node().contents.iter() {
                // self.items_to_lower.push(expr.ast_ref());
            }
        }

        Ok(())
    }
}
