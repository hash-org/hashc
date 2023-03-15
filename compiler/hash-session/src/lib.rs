//! Defines the global Hash compiler state. This is used to create
//! a global [CompilerSession] which holds all of the information that
//! might be used by multiple stages across the entire compiler pipeline.
//!
//! However, the [CompilerSession] is opaque to all of the stages within
//! the pipeline. Each [CompilerStage] must provide a trait that provides
//! methods for "selecting" the information that is needed by the stage.
//! This creates a clear separation between the stages and the global state,
//! keeping the crate dependency graph clean.

use std::collections::HashSet;

use hash_ast::node_map::NodeMap;
use hash_ast_desugaring::{AstDesugaringCtx, AstDesugaringCtxQuery, AstDesugaringPass};
use hash_ast_expand::{AstExpansionCtx, AstExpansionCtxQuery, AstExpansionPass};
use hash_backend::{BackendCtxQuery, CodeGenPass};
use hash_codegen::backend::BackendCtx;
use hash_ir::IrStorage;
use hash_layout::LayoutCtx;
use hash_link::{CompilerLinker, LinkerCtx, LinkerCtxQuery};
use hash_lower::{IrGen, IrOptimiser, LoweringCtx, LoweringCtxQuery};
use hash_parser::{Parser, ParserCtx, ParserCtxQuery};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerOutputStream, CompilerStage},
    settings::CompilerSettings,
    workspace::Workspace,
};
use hash_reporting::{report::Report, writer::ReportWriter};
use hash_semantics::{
    old::{Typechecker, TypecheckingCtx, TypecheckingCtxQuery},
    Flags, SemanticAnalysis, SemanticAnalysisCtx, SemanticAnalysisCtxQuery, SemanticStorage,
};
use hash_source::{entry_point::EntryPointState, SourceId, SourceMap};
use hash_tir::old::storage::{GlobalStorage, LocalStorage, TyStorage};
use hash_untyped_semantics::{
    UntypedSemanticAnalysis, UntypedSemanticAnalysisCtx, UntypedSemanticAnalysisCtxQuery,
};
use hash_utils::stream_less_ewriteln;

/// Function to make all of the stages a nominal compiler pipeline accepts.
pub fn make_stages() -> Vec<Box<dyn CompilerStage<CompilerSession>>> {
    vec![
        Box::new(Parser),
        Box::new(AstDesugaringPass),
        Box::new(AstExpansionPass),
        Box::new(UntypedSemanticAnalysis),
        // @@Temporary: remove this when old typechecker is removed.
        if std::env::var("USE_OLD_TC").is_ok() {
            Box::new(Typechecker::new())
        } else {
            Box::new(SemanticAnalysis)
        },
        Box::<IrGen>::default(),
        Box::<IrOptimiser>::default(),
        Box::<CodeGenPass>::default(),
        Box::new(CompilerLinker),
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

    // Semantic analysis storage
    pub semantic_storage: SemanticStorage,

    /// Sources that have passed from the `expansion` stage of the compiler.
    /// @@Todo: Use bit-flags to represent which module has been
    /// expanded/desugared/semantically checked/type checked.
    pub expanded_sources: HashSet<SourceId>,

    /// Sources that have passed from the `desugaring` stage of the compiler.
    pub desugared_modules: HashSet<SourceId>,

    /// Modules that have already been semantically checked. This is needed in
    /// order to avoid re-checking modules on re-evaluations of a workspace.
    pub semantically_checked_modules: HashSet<SourceId>,

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
            semantic_storage: SemanticStorage::new(),
            ir_storage: IrStorage::new(),
            layout_storage: LayoutCtx::new(layout_info),
            ty_storage: TyStorage { global, local, entry_point_state: EntryPointState::new() },
            expanded_sources: HashSet::new(),
            desugared_modules: HashSet::new(),
            semantically_checked_modules: HashSet::new(),
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

impl UntypedSemanticAnalysisCtxQuery for CompilerSession {
    fn data(&mut self) -> UntypedSemanticAnalysisCtx {
        UntypedSemanticAnalysisCtx { workspace: &mut self.workspace, pool: &self.pool }
    }
}

impl AstExpansionCtxQuery for CompilerSession {
    fn data(&mut self) -> AstExpansionCtx {
        let output_stream = self.output_stream();
        AstExpansionCtx {
            workspace: &mut self.workspace,
            settings: &self.settings,
            stdout: output_stream,
        }
    }
}

impl SemanticAnalysisCtxQuery for CompilerSession {
    fn data(&mut self) -> SemanticAnalysisCtx {
        SemanticAnalysisCtx {
            workspace: &mut self.workspace,
            semantic_storage: &mut self.semantic_storage,
            flags: Flags {
                dump_tir: self.settings.semantic_settings.dump_tir,
                eval_tir: self.settings.semantic_settings.eval_tir,
                mono_tir: self.settings.semantic_settings.mono_tir,
                run_to_stage: self.settings.stage,
            },
            target: self.settings.target(),
        }
    }
}

impl LoweringCtxQuery for CompilerSession {
    fn data(&mut self) -> LoweringCtx {
        let output_stream = self.output_stream();
        LoweringCtx {
            semantic_storage: &self.semantic_storage,
            workspace: &mut self.workspace,
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

impl LinkerCtxQuery for CompilerSession {
    fn data(&mut self) -> hash_link::LinkerCtx<'_> {
        let stdout = self.output_stream();

        LinkerCtx { workspace: &self.workspace, settings: &self.settings, stdout }
    }
}

impl TypecheckingCtxQuery for CompilerSession {
    fn data(&mut self) -> TypecheckingCtx {
        TypecheckingCtx {
            settings: &self.settings,
            workspace: &mut self.workspace,
            ty_storage: &mut self.ty_storage,
        }
    }
}
