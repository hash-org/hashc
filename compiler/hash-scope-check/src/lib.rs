//! This crate is responsible for performing scoping analysis on the Hash AST.
//!
//! The lexical analysis pass occurs after the AST expansion and desugaring, and
//! just before the type checking pass. Here, all names are resolved to their
//! corresponding definitions, and scopes of definitions are gathered and
//! indexed by AST node IDs.
//!
//! This pass also checks for recursive definitions, and reports an error if
//! a recursive definition is invalid.
#![feature(unwrap_infallible, never_type)]

use ast::{AstNameData, AstNameDataVisitor};
use hash_ast::{ast::OwnsAstNode, node_map::SourceRef, visitor::AstVisitorMutSelf};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerResult, CompilerStage},
    settings::{CompilerSettings, CompilerStageKind},
    workspace::Workspace,
};
use hash_source::SourceId;
use hash_utils::timing::{CellStageMetrics, StageMetrics};
pub mod ast;
pub mod referencing;

/// The Hash name analysis and checking compiler stage.
#[derive(Default)]
pub struct ScopeCheck {
    /// The metrics of the name checking stage.
    metrics: CellStageMetrics,
}

/// All of the information that is required
/// from the compiler state for the scope checking stage to operate.
pub struct ScopeCheckCtx<'env> {
    /// The workspace. This is used to retrieve the AST and other
    /// information about the source.
    pub workspace: &'env Workspace,

    /// The AST name checking output. This is managed by this crate.
    pub name_data: &'env mut AstNameData,

    /// The user-given settings to semantic analysis.
    pub settings: &'env CompilerSettings,
}

pub trait ScopeCheckCtxQuery: CompilerInterface {
    fn data(&mut self) -> ScopeCheckCtx;
}

impl<Ctx: ScopeCheckCtxQuery> CompilerStage<Ctx> for ScopeCheck {
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::ScopeCheck
    }

    fn run(&mut self, entry_point: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let ctx = ctx.data();
        let mut visitor =
            AstNameDataVisitor { current_scopes: Vec::new(), name_data: ctx.name_data };

        let entry_point_source = ctx.workspace.node_map.get_source(entry_point);

        match entry_point_source {
            SourceRef::Interactive(interactive) => {
                let node = interactive.node();
                visitor.visit_body_block(node.ast_ref()).into_ok();
            }
            SourceRef::Module(module) => {
                let node = module.node();
                visitor.visit_module(node.ast_ref()).into_ok();
            }
        }

        println!("Finalised name tree: {:#?}", ctx.name_data);

        Ok(())
    }

    fn metrics(&self) -> StageMetrics {
        self.metrics.clone().into()
    }

    fn cleanup(&mut self, _entry_point: SourceId, _stage_data: &mut Ctx) {}
}
