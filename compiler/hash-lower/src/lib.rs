//! Hash Intermediate Representation builder. This crate contains the
//! functionality that converts the Hash typed AST into Hash IR. Additionally,
//! the Hash IR builder crate contains implemented passes that will optimise the
//! IR, performing optimisations such as constant folding or dead code
//! elimination.
#![allow(unused)] // @@TODO: remove this when the builder is complete

pub mod builder;
mod cfg;
mod visitor;

use hash_ast::ast::{AstNodeRef, AstVisitor, Expr, OwnsAstNode};
use hash_ir::ir::Body;
use hash_pipeline::{
    interface::{CompilerInterface, CompilerResult, CompilerStage},
    settings::CompilerStageKind,
    workspace::Workspace,
};
use hash_source::{
    location::{SourceLocation, Span},
    SourceId,
};
use hash_types::storage::TyStorage;
use visitor::LoweringVisitor;

use self::builder::Builder;

/// The [IrLowerer] is used as a bootstrapping mechanism to kick off the
/// [Builder] working on functions that it discovers as the the lower traverses
/// through the source files.
pub struct IrLowerer;

impl IrLowerer {
    pub fn new() -> Self {
        Self
    }
}

impl Default for IrLowerer {
    fn default() -> Self {
        Self::new()
    }
}

pub trait IrLoweringCtx: CompilerInterface {
    fn data(&mut self) -> (&Workspace, &mut TyStorage);
}

impl<Ctx: IrLoweringCtx> CompilerStage<Ctx> for IrLowerer {
    fn stage_kind(&self) -> CompilerStageKind {
        CompilerStageKind::IrGen
    }

    fn run_stage(&mut self, entry_point: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let (workspace, ty_storage) = ctx.data();

        // We need to iterate all of the modules and essentially perform
        // a discovery process for what needs to be lowered...
        let discoverer = LoweringVisitor::new(&ty_storage.global);

        // We need to visit all of the modules in the workspace and discover
        // what needs to be lowered.
        for (module_id, module) in workspace.node_map.iter_modules() {
            discoverer.visit_module(module.node_ref());
        }

        Ok(())
    }
}
