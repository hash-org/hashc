//! The Hash semantic analyser.
//!
//! This brings light to the world by ensuring the correctness of the crude and
//! dangerous Hash program that is given as input to the compiler.

#![feature(
    decl_macro,
    slice_pattern,
    option_result_contains,
    let_chains,
    if_let_guard,
    cell_update,
    try_blocks
)]

use diagnostics::error::SemanticError;
use environment::{
    ast_info::AstInfo,
    sem_env::{AccessToSemEnv, DiagnosticsStore, PreludeOrUnset, SemEnv},
};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::CompilerStageKind,
    workspace::Workspace,
    CompilerResult,
};
use hash_reporting::diagnostic::Diagnostics;
use hash_source::SourceId;
use hash_tir::environment::{
    context::Context, env::Env, source_info::CurrentSourceInfo, stores::Stores,
};
use once_cell::unsync::OnceCell;
use ops::{
    bootstrap::{DefinedIntrinsicsOrUnset, DefinedPrimitivesOrUnset},
    common::CommonOps,
};

pub mod diagnostics;
pub mod environment;
pub mod old;
pub mod ops;
pub mod passes;

/// The Hash semantic analysis compiler stage.

/// @@Docs: overview of each analysis pass.
#[derive(Default)]
pub struct SemanticAnalysis;

/// Flags to the semantic analysis stage.
#[derive(Debug, Clone, Copy)]
pub struct Flags {
    /// Evaluate the generated TIR.
    pub eval_tir: bool,

    /// Dump the generated TIR.
    pub dump_tir: bool,
}

/// The [SemanticAnalysisCtx] represents all of the information that is required
/// from the compiler state for the semantic analysis stage to operate.
pub struct SemanticAnalysisCtx<'tc> {
    /// The workspace. This is used to retrieve the AST and other
    /// information about the source.
    pub workspace: &'tc Workspace,

    /// The semantic storage. This is managed by this crate.
    ///
    /// It contains stores, environments, context, etc. for semantic
    /// analysis and typechecking.
    pub semantic_storage: &'tc mut SemanticStorage,

    /// The user-given settings to semantic analysis.
    pub flags: Flags,
}

pub trait SemanticAnalysisCtxQuery: CompilerInterface {
    fn data(&mut self) -> SemanticAnalysisCtx;
}

/// Semantic storage is a collection of stores, environments, and other
/// information that is required for semantic analysis and typechecking.
///
/// From it, `Env` and `SemEnv` are constructed as ref-containing structs.
pub struct SemanticStorage {
    /// TIR:
    pub stores: Stores,
    pub context: Context,

    /// Diagnostics store.
    pub diagnostics: DiagnosticsStore,

    /// AST information mapped to TIR terms.
    pub ast_info: AstInfo,

    // Bootstrapping:
    pub prelude_or_unset: PreludeOrUnset,
    pub primitives_or_unset: DefinedPrimitivesOrUnset,
    pub intrinsics_or_unset: DefinedIntrinsicsOrUnset,
}

impl SemanticStorage {
    pub fn new() -> Self {
        Self {
            stores: Stores::new(),
            context: Context::new(),
            diagnostics: DiagnosticsStore::new(),
            ast_info: AstInfo::new(),
            prelude_or_unset: OnceCell::new(),
            primitives_or_unset: OnceCell::new(),
            intrinsics_or_unset: OnceCell::new(),
        }
    }
}

impl Default for SemanticStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl<Ctx: SemanticAnalysisCtxQuery> CompilerStage<Ctx> for SemanticAnalysis {
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::Analysis
    }

    fn run(&mut self, entry_point: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let SemanticAnalysisCtx { workspace, semantic_storage, flags } = ctx.data();
        let current_source_info = CurrentSourceInfo { source_id: entry_point };

        // Construct the core TIR environment.
        let env = Env::new(
            &semantic_storage.stores,
            &semantic_storage.context,
            &workspace.node_map,
            &workspace.source_map,
            &current_source_info,
        );

        // Construct the semantic analysis environment.
        let sem_env = SemEnv::new(
            &env,
            &semantic_storage.diagnostics,
            &semantic_storage.ast_info,
            &semantic_storage.prelude_or_unset,
            &semantic_storage.primitives_or_unset,
            &semantic_storage.intrinsics_or_unset,
            &flags,
        );

        // Visit the sources
        let visitor = passes::Visitor::new(&sem_env);
        sem_env.try_or_add_error(visitor.visit_source());

        if visitor.sem_env().diagnostics().has_errors() {
            // @@Todo: warnings
            let (errors, _warnings) = visitor.sem_env().diagnostics().into_diagnostics();
            return Err(visitor.sem_env().with(&SemanticError::Compound { errors }).into());
        } else {
            // Passed!
            Ok(())
        }
    }

    fn cleanup(&mut self, _entry_point: SourceId, _stage_data: &mut Ctx) {}
}
