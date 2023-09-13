//! The Hash semantic analyser.
//!
//! This brings light to the world by ensuring the correctness of the crude and
//! dangerous Hash program that is given as input to the compiler.

#![feature(decl_macro, slice_pattern, let_chains, if_let_guard, cell_update, try_blocks)]

use diagnostics::{
    definitions::{SemanticError, SemanticWarning},
    reporting::SemanticReporter,
};
use env::{HasSemanticDiagnostics, SemanticEnv};
use hash_ast::node_map::{HasNodeMap, NodeMap};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerResult, CompilerStage},
    settings::{CompilerSettings, CompilerStageKind},
    workspace::Workspace,
};
use hash_reporting::diagnostic::{DiagnosticCellStore, Diagnostics, HasDiagnostics};
use hash_source::SourceId;
use storage::SemanticStorage;

pub mod bootstrap;
pub mod current_source;
pub mod diagnostics;
pub mod env;
pub mod environment;
pub mod passes;
pub mod prelude;
pub mod progress;
pub mod storage;

/// The Hash semantic analysis compiler stage.

#[derive(Default)]
pub struct SemanticAnalysis;

/// The [SemanticAnalysisCtx] represents all of the information that is required
/// from the compiler state for the semantic analysis stage to operate.
pub struct SemanticAnalysisCtx<'env> {
    /// The workspace. This is used to retrieve the AST and other
    /// information about the source.
    pub workspace: &'env Workspace,

    /// The semantic storage. This is managed by this crate.
    ///
    /// It contains stores, environments, context, etc. for semantic
    /// analysis and typechecking.
    pub semantic_storage: &'env mut SemanticStorage,

    /// The user-given settings to semantic analysis.
    pub settings: &'env CompilerSettings,
}

pub trait SemanticAnalysisCtxQuery: CompilerInterface {
    fn data(&mut self) -> SemanticAnalysisCtx;
}

impl<Ctx: SemanticAnalysisCtxQuery> CompilerStage<Ctx> for SemanticAnalysis {
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::Analysis
    }

    fn run(&mut self, entry_point: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        // Create the semantic environment
        let env = SemanticEnvImpl { ctx: ctx.data(), diagnostics: DiagnosticCellStore::new() };

        // Visit the sources by first visiting the entry point
        //
        // The rest of the sources will be visited by the analyser
        let analyser = passes::Analyser::new(&env);
        analyser.try_or_add_error(analyser.visit_source(entry_point));

        // Handle any diagnostics that were emitted
        if env.diagnostics().has_diagnostics() {
            Err(env.diagnostics().into_reports(
                SemanticReporter::make_reports_from_error,
                SemanticReporter::make_reports_from_warning,
            ))
        } else {
            Ok(())
        }
    }

    fn cleanup(&mut self, _entry_point: SourceId, _stage_data: &mut Ctx) {}
}

/// The `SemanticEnv` trait can be implemented through access to the
/// `SemanticAnalysisCtx`, as well as a fresh store for diagnostics.
pub struct SemanticEnvImpl<'env> {
    ctx: SemanticAnalysisCtx<'env>,
    diagnostics: DiagnosticCellStore<SemanticError, SemanticWarning>,
}

impl HasNodeMap for SemanticEnvImpl<'_> {
    fn node_map(&self) -> &NodeMap {
        &self.ctx.workspace.node_map
    }
}

impl HasDiagnostics for SemanticEnvImpl<'_> {
    type Diagnostics = DiagnosticCellStore<SemanticError, SemanticWarning>;

    fn diagnostics(&self) -> &Self::Diagnostics {
        &self.diagnostics
    }
}

impl HasSemanticDiagnostics for SemanticEnvImpl<'_> {
    type SemanticDiagnostics = DiagnosticCellStore<SemanticError, SemanticWarning>;
}

impl SemanticEnv for SemanticEnvImpl<'_> {
    fn storage(&self) -> &SemanticStorage {
        self.ctx.semantic_storage
    }

    fn storage_mut(&mut self) -> &mut SemanticStorage {
        self.ctx.semantic_storage
    }
}
