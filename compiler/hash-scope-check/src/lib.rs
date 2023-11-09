//! This crate is responsible for performing scoping analysis on the Hash AST.
//!
//! The lexical analysis pass occurs after the AST expansion and desugaring, and
//! just before the type checking pass. Here, all names are resolved to their
//! corresponding definitions, and scopes of definitions are gathered and
//! indexed by AST node IDs.
//!
//! This pass also checks for recursive definitions, and reports an error if
//! a recursive definition is invalid.
#![feature(unwrap_infallible, never_type, let_chains)]

use hash_pipeline::{
    interface::{CompilerInterface, CompilerResult, CompilerStage},
    settings::{CompilerSettings, CompilerStageKind},
    workspace::Workspace,
};
use hash_reporting::diagnostic::DiagnosticsMut;
use hash_source::SourceId;
use hash_utils::timing::{CellStageMetrics, StageMetrics};
use scope::AllScopeData;
use visitor::ScopeCheckVisitor;

pub mod diagnostics;
pub mod referencing;
pub mod scope;
pub mod visitor;

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

    /// The AST scope checking output. This is managed by this crate.
    pub scope_data: &'env mut AllScopeData,

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
        let scope_data = ctx.scope_data.get_for_source(entry_point);
        let source = ctx.workspace.node_map.get_source(entry_point);
        let mut visitor = ScopeCheckVisitor::run_on_source(source, scope_data);

        if visitor.diagnostics.has_diagnostics() {
            let reports = visitor.diagnostics.into_reports_from_reporter();
            Err(reports)
        } else {
            Ok(())
        }
    }

    fn metrics(&self) -> StageMetrics {
        self.metrics.clone().into()
    }

    fn cleanup(&mut self, _entry_point: SourceId, _stage_data: &mut Ctx) {}
}
