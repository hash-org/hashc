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
use hash_backend::{BackendCtxQuery, CodeGenPass};
use hash_codegen::backend::BackendCtx;
use hash_ir::IrStorage;
use hash_layout::LayoutCtx;
use hash_lower::{IrGen, IrOptimiser, LoweringCtx, LoweringCtxQuery};
use hash_parser::{Parser, ParserCtx, ParserCtxQuery};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerOutputStream, CompilerStage},
    settings::CompilerSettings,
    workspace::Workspace,
};
use hash_reporting::{report::Report, writer::ReportWriter};
use hash_semantics::{Typechecker, TypecheckingCtx, TypecheckingCtxQuery};
use hash_source::{entry_point::EntryPointState, SourceId, SourceMap};
use hash_tir::storage::{GlobalStorage, LocalStorage, TyStorage};
use hash_untyped_semantics::{SemanticAnalysis, SemanticAnalysisCtx, SemanticAnalysisCtxQuery};
use hash_utils::stream_less_ewriteln;

/// Function to make all of the stages a nominal compiler pipeline accepts.
pub fn make_stages() -> Vec<Box<dyn CompilerStage<CompilerSession>>> {
    vec![
        Box::new(Parser),
        Box::new(AstDesugaringPass),
        Box::new(AstExpansionPass),
        Box::new(SemanticAnalysis),
        Box::new(Typechecker::new()),
        Box::<IrGen>::default(),
        Box::new(IrOptimiser),
        Box::new(CodeGenPass),
    ]
}

/// Emit a fatal compiler error and exit the compiler. These kind of errors are
/// not **panics** but they are neither recoverable. This function will convert
/// the error into a [Report] and then write it to the error stream.
pub fn emit_fatal_error<E: Into<Report>>(error: E, sources: &SourceMap) -> ! {
    stream_less_ewriteln!("{}", ReportWriter::single(error.into(), sources));
    std::process::exit(-1);
}

/// The [CompilerSession] holds all the information and state of the compiler
/// instance. Each stage of the compiler contains a `State` type parameter which
/// the compiler stores so that incremental executions of the compiler are
/// possible.
pub struct CompilerSession {
    /// The collected workspace sources for the current job.
    pub workspace: Workspace,

    /// The stream to use for writing diagnostics to.
    pub error_stream: Box<dyn Fn() -> CompilerOutputStream>,

    /// The stream to use for writing output to.
    pub output_stream: Box<dyn Fn() -> CompilerOutputStream>,

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
    pub layout_storage: LayoutCtx,
}

impl CompilerSession {
    /// Create a new [CompilerSession].
    pub fn new(
        workspace: Workspace,
        pool: rayon::ThreadPool,
        settings: CompilerSettings,
        error_stream: impl Fn() -> CompilerOutputStream + 'static,
        output_stream: impl Fn() -> CompilerOutputStream + 'static,
    ) -> Self {
        let target = settings.target();

        // @@Fixme: ideally this error should be handled else-where
        let layout_info = target
            .parse_data_layout()
            .unwrap_or_else(|err| emit_fatal_error(err, &workspace.source_map));

        let global = GlobalStorage::new(target);
        let local = LocalStorage::new(&global, SourceId::default());

        Self {
            error_stream: Box::new(error_stream),
            output_stream: Box::new(output_stream),
            workspace,
            diagnostics: Vec::new(),
            pool,
            settings,
            ty_storage: TyStorage { global, local, entry_point_state: EntryPointState::new() },
            ir_storage: IrStorage::new(),
            layout_storage: LayoutCtx::new(layout_info),
        }
    }
}

impl CompilerInterface for CompilerSession {
    /// Get a reference to the error [CompilerOutputStream].
    fn error_stream(&self) -> CompilerOutputStream {
        (self.error_stream)()
    }

    /// Get a reference to the output [CompilerOutputStream].
    fn output_stream(&self) -> CompilerOutputStream {
        (self.output_stream)()
    }

    /// Get a reference to the [CompilerSettings].
    fn settings(&self) -> &CompilerSettings {
        &self.settings
    }

    /// Get a mutable reference to the [CompilerSettings].
    fn settings_mut(&mut self) -> &mut CompilerSettings {
        &mut self.settings
    }

    /// Get a reference to the current diagnostic collection.
    fn diagnostics(&self) -> &[Report] {
        &self.diagnostics
    }

    /// Get a mutable reference to the current diagnostic collection.
    fn diagnostics_mut(&mut self) -> &mut Vec<Report> {
        &mut self.diagnostics
    }

    /// Get a reference to the current [Workspace].
    fn workspace(&self) -> &Workspace {
        &self.workspace
    }

    /// Get a mutable reference to the current [Workspace].
    fn workspace_mut(&mut self) -> &mut Workspace {
        &mut self.workspace
    }

    /// Get a reference to [NodeMap] for the current [Workspace].
    fn node_map(&self) -> &NodeMap {
        &self.workspace.node_map
    }

    /// Get a reference to [SourceMap] for the current [Workspace].
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
        let output_stream = self.output_stream();
        AstExpansionCtx { workspace: &mut self.workspace, stdout: output_stream }
    }
}

impl TypecheckingCtxQuery for CompilerSession {
    fn data(&mut self) -> TypecheckingCtx {
        TypecheckingCtx {
            workspace: &mut self.workspace,
            ty_storage: &mut self.ty_storage,
            settings: &self.settings,
        }
    }
}

impl LoweringCtxQuery for CompilerSession {
    fn data(&mut self) -> LoweringCtx {
        let output_stream = self.output_stream();
        LoweringCtx {
            workspace: &mut self.workspace,
            ty_storage: &self.ty_storage,
            settings: &self.settings,
            layout_storage: &self.layout_storage,
            ir_storage: &mut self.ir_storage,
            stdout: output_stream,
            _pool: &self.pool,
        }
    }
}

impl BackendCtxQuery for CompilerSession {
    fn data(&mut self) -> BackendCtx {
        let output_stream = self.output_stream();

        BackendCtx {
            workspace: &mut self.workspace,
            ir_storage: &self.ir_storage,
            layout_storage: &self.layout_storage,
            settings: &self.settings,
            stdout: output_stream,
            _pool: &self.pool,
        }
    }
}
