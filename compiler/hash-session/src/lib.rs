//! Defines the global Hash compiler state. This is used to create
//! a global [CompilerSession] which holds all of the information that
//! might be used by multiple stages across the entire compiler pipeline.
//!
//! However, the [CompilerSession] is opaque to all of the stages within
//! the pipeline. Each [CompilerStage] must provide a trait that provides
//! methods for "selecting" the information that is needed by the stage.
//! This creates a clear separation between the stages and the global state,
//! keeping the crate dependency graph clean.

use hash_ast::node_map::NodeMap;
use hash_ast_desugaring::{AstDesugaringCtx, AstDesugaringPass};
use hash_ast_expand::{AstExpansionCtx, AstExpansionPass};
use hash_lower::{AstLowerer, IrLoweringCtx};
use hash_parser::{Parser, ParserCtx};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::CompilerSettings,
    workspace::Workspace,
};
use hash_reporting::report::Report;
use hash_source::{SourceId, SourceMap};
use hash_typecheck::{Typechecker, TypecheckingCtx};
use hash_types::storage::{GlobalStorage, LocalStorage, TyStorage};
use hash_untyped_semantics::{SemanticAnalysis, SemanticAnalysisCtx};
use hash_vm::{vm::Interpreter, InterpreterCtx};

/// Function to make all of the stages a nominal compiler pipeline accepts.
pub fn make_stages() -> Vec<Box<dyn CompilerStage<CompilerSession>>> {
    vec![
        Box::new(Parser::new()),
        Box::new(AstExpansionPass),
        Box::new(AstDesugaringPass),
        Box::new(SemanticAnalysis),
        Box::new(Typechecker::new()),
        Box::new(AstLowerer::new()),
        Box::new(Interpreter::new()),
    ]
}

/// The [CompilerSession] holds all the information and state of the compiler
/// instance. Each stage of the compiler contains a `State` type parameter which
/// the compiler stores so that incremental executions of the compiler are
/// possible.
pub struct CompilerSession {
    /// The collected workspace sources for the current job.
    pub workspace: Workspace,
    /// Any diagnostics that were collected from any stage
    pub diagnostics: Vec<Report>,

    /// The shared compiler thread pool.
    pub pool: rayon::ThreadPool,

    /// Compiler settings that are stored.
    pub settings: CompilerSettings,

    /// Compiler type storage. Stores all the types that are created during
    /// the typechecking stage, which is used for later stages during code
    /// generation.
    pub ty_storage: TyStorage,
}

impl CompilerSession {
    pub fn new(workspace: Workspace, pool: rayon::ThreadPool, settings: CompilerSettings) -> Self {
        let global = GlobalStorage::new();
        let local = LocalStorage::new(&global, SourceId::default());

        Self {
            workspace,
            diagnostics: Vec::new(),
            pool,
            settings,
            ty_storage: TyStorage { global, local },
        }
    }
}

impl CompilerInterface for CompilerSession {
    fn settings(&self) -> &CompilerSettings {
        &self.settings
    }

    fn settings_mut(&mut self) -> &mut CompilerSettings {
        &mut self.settings
    }

    fn diagnostics(&self) -> &[Report] {
        &self.diagnostics
    }

    fn diagnostics_mut(&mut self) -> &mut Vec<Report> {
        &mut self.diagnostics
    }

    fn workspace(&self) -> &Workspace {
        &self.workspace
    }

    fn workspace_mut(&mut self) -> &mut Workspace {
        &mut self.workspace
    }

    fn node_map(&self) -> &NodeMap {
        &self.workspace.node_map
    }

    fn source_map(&self) -> &SourceMap {
        &self.workspace.source_map
    }
}

impl ParserCtx for CompilerSession {
    fn data(&mut self) -> (&mut Workspace, &rayon::ThreadPool) {
        (&mut self.workspace, &self.pool)
    }
}

impl AstDesugaringCtx for CompilerSession {
    fn data(&mut self) -> (&mut Workspace, &rayon::ThreadPool) {
        (&mut self.workspace, &self.pool)
    }
}

impl SemanticAnalysisCtx for CompilerSession {
    fn data(&mut self) -> (&mut Workspace, &rayon::ThreadPool) {
        (&mut self.workspace, &self.pool)
    }
}

impl AstExpansionCtx for CompilerSession {
    fn data(&mut self) -> &mut Workspace {
        &mut self.workspace
    }
}

impl TypecheckingCtx for CompilerSession {
    fn data(&mut self) -> (&Workspace, &mut TyStorage) {
        (&self.workspace, &mut self.ty_storage)
    }
}

impl IrLoweringCtx for CompilerSession {
    fn data(&mut self) -> (&Workspace, &mut TyStorage) {
        (&self.workspace, &mut self.ty_storage)
    }
}

impl InterpreterCtx for CompilerSession {}
