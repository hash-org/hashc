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
use hash_ast_desugaring::{AstDesugaringCtx, AstDesugaringCtxQuery, AstDesugaringPass};
use hash_ast_expand::{AstExpansionCtx, AstExpansionCtxQuery, AstExpansionPass};
use hash_backend::{BackendCtx, BackendCtxQuery, HashBackend};
use hash_ir::IrStorage;
use hash_layout::LayoutStorage;
use hash_lower::{IrGen, IrOptimiser, LoweringCtx, LoweringCtxQuery};
use hash_parser::{Parser, ParserCtx, ParserCtxQuery};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::CompilerSettings,
    workspace::Workspace,
};
use hash_reporting::report::Report;
use hash_source::{SourceId, SourceMap};
use hash_typecheck::{Typechecker, TypecheckingCtx, TypecheckingCtxQuery};
use hash_types::storage::{GlobalStorage, LocalStorage, TyStorage};
use hash_untyped_semantics::{SemanticAnalysis, SemanticAnalysisCtx, SemanticAnalysisCtxQuery};

/// Function to make all of the stages a nominal compiler pipeline accepts.
pub fn make_stages() -> Vec<Box<dyn CompilerStage<CompilerSession>>> {
    vec![
        Box::new(Parser),
        Box::new(AstExpansionPass),
        Box::new(AstDesugaringPass),
        Box::new(SemanticAnalysis),
        Box::new(Typechecker::new()),
        Box::new(IrGen),
        Box::new(IrOptimiser),
        Box::new(HashBackend::new()),
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

    /// Compiler IR storage. Stores all the IR that is created during the
    /// lowering stage, which is used for later stages during code generation.
    pub ir_storage: IrStorage,

    /// Storage for all of the [Layout]s that have been created
    /// for the IR. Additionally, this also stores a cache for
    /// the looking up resultant [Layout]s by the specific IR type
    /// ID.
    pub layout_storage: LayoutStorage,
}

impl CompilerSession {
    /// Create a new [CompilerSession].
    pub fn new(workspace: Workspace, pool: rayon::ThreadPool, settings: CompilerSettings) -> Self {
        let target = settings.codegen_settings().target_info.target();
        let layout_info = settings.codegen_settings().layout.clone();

        let global = GlobalStorage::new(target);
        let local = LocalStorage::new(&global, SourceId::default());

        Self {
            workspace,
            diagnostics: Vec::new(),
            pool,
            settings,
            ty_storage: TyStorage { global, local },
            ir_storage: IrStorage::new(),
            layout_storage: LayoutStorage::new(layout_info),
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

impl ParserCtxQuery for CompilerSession {
    fn data(&mut self) -> ParserCtx {
        ParserCtx { workspace: &mut self.workspace, pool: &self.pool }
    }
}

impl AstDesugaringCtxQuery for CompilerSession {
    fn data(&mut self) -> AstDesugaringCtx {
        AstDesugaringCtx { workspace: &mut self.workspace, pool: &self.pool }
    }
}

impl SemanticAnalysisCtxQuery for CompilerSession {
    fn data(&mut self) -> SemanticAnalysisCtx {
        SemanticAnalysisCtx { workspace: &mut self.workspace, pool: &self.pool }
    }
}

impl AstExpansionCtxQuery for CompilerSession {
    fn data(&mut self) -> AstExpansionCtx {
        AstExpansionCtx { workspace: &mut self.workspace }
    }
}

impl TypecheckingCtxQuery for CompilerSession {
    fn data(&mut self) -> TypecheckingCtx {
        TypecheckingCtx { workspace: &mut self.workspace, ty_storage: &mut self.ty_storage }
    }
}

impl LoweringCtxQuery for CompilerSession {
    fn data(&mut self) -> LoweringCtx {
        LoweringCtx {
            workspace: &mut self.workspace,
            ty_storage: &self.ty_storage,
            settings: &self.settings,
            ir_storage: &mut self.ir_storage,
            _pool: &self.pool,
        }
    }
}

impl BackendCtxQuery for CompilerSession {
    fn data(&mut self) -> BackendCtx {
        BackendCtx {
            workspace: &mut self.workspace,
            ir_storage: &self.ir_storage,
            settings: self.settings.codegen_settings(),
            _pool: &self.pool,
        }
    }
}
