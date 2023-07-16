//! Defines the global Hash compiler state. This is used to create
//! a global [DefaultCompilerInterface] which holds all of the information that
//! might be used by multiple stages across the entire compiler pipeline.
//!
//! However, the [DefaultCompilerInterface] is opaque to all of the stages
//! within the pipeline. Each [CompilerStage] must provide a trait that provides
//! methods for "selecting" the information that is needed by the stage.
//! This creates a clear separation between the stages and the global state,
//! keeping the crate dependency graph clean.
pub mod driver;

use std::collections::HashSet;

use driver::Driver;
use hash_ast::node_map::NodeMap;
use hash_ast_desugaring::{AstDesugaringCtx, AstDesugaringCtxQuery, AstDesugaringPass};
use hash_ast_expand::{AstExpansionCtx, AstExpansionCtxQuery, AstExpansionPass};
use hash_backend::{BackendCtxQuery, CodeGenPass};
use hash_codegen::backend::{BackendCtx, CodeGenStorage};
use hash_ir::IrStorage;
use hash_layout::LayoutCtx;
use hash_link::{CompilerLinker, LinkerCtx, LinkerCtxQuery};
use hash_lower::{IrGen, IrOptimiser, LoweringCtx, LoweringCtxQuery};
use hash_parser::{Parser, ParserCtx, ParserCtxQuery};
use hash_pipeline::{
    error::PipelineError,
    interface::{CompilerInterface, CompilerOutputStream, CompilerStage},
    settings::CompilerSettings,
    workspace::Workspace,
};
use hash_reporting::report::Report;
use hash_semantics::{
    SemanticAnalysis, SemanticAnalysisCtx, SemanticAnalysisCtxQuery, SemanticStorage,
};
use hash_source::{SourceId, SourceMap};
use hash_untyped_semantics::{
    UntypedSemanticAnalysis, UntypedSemanticAnalysisCtx, UntypedSemanticAnalysisCtxQuery,
};

/// A struct that is used to construct a [Compiler] with
/// either a default or a custom configuration.
/// @@Naming
pub struct CompilerBuilder;

impl CompilerBuilder {
    /// Create a new [Compiler] with the default stage configuration.
    pub fn build_with_settings(settings: CompilerSettings) -> Driver<Compiler> {
        let session = utils::emit_on_fatal_error(|| Compiler::new(settings));
        Self::build_with_interface(session)
    }

    /// Create a new [Compiler] with a specified compiler interface that
    /// supports the [DefaultCtxQuery] trait, i.e. all of the stages within
    /// the standard pipeline.
    pub fn build_with_interface<I: CompilerInterface + DefaultCtxQuery>(interface: I) -> Driver<I> {
        Self::build(
            interface,
            vec![
                Box::new(Parser),
                Box::new(AstDesugaringPass),
                Box::new(AstExpansionPass),
                Box::new(UntypedSemanticAnalysis),
                Box::new(SemanticAnalysis),
                Box::<IrGen>::default(),
                Box::<IrOptimiser>::default(),
                Box::<CodeGenPass>::default(),
                Box::<CompilerLinker>::default(),
            ],
        )
    }

    /// Create a new [Compiler] with a custom configuration.
    ///
    /// This will automatically run the `bootstrap` method of the
    /// compiler in order to initialise the compiler.
    pub fn build<I: CompilerInterface>(
        ctx: I,
        stages: Vec<Box<dyn CompilerStage<I>>>,
    ) -> Driver<I> {
        let mut compiler = Driver::new(ctx, stages);

        compiler.bootstrap();
        compiler
    }
}

pub mod utils {
    use hash_reporting::{report::Report, writer::ReportWriter};
    use hash_source::SourceMap;
    use hash_utils::stream_less_ewriteln;

    /// Emit a fatal compiler error and exit the compiler. These kind of errors
    /// are not **panics** but they are neither recoverable. This function
    /// will convert the error into a [Report] and then write it to the
    /// error stream.
    pub fn emit_fatal_error<E: Into<Report>>(error: E, sources: &SourceMap) -> ! {
        stream_less_ewriteln!("{}", ReportWriter::single(error.into(), sources));
        std::process::exit(-1);
    }

    /// Perform some task that might fail and if it does, report the error and
    /// exit, otherwise return the result of the task.
    ///
    /// The error type is intentionally not specified so that this function can
    /// be used in contexts where the error type is known to implementing the
    /// [Into<Report>] trait.
    pub fn emit_on_fatal_error<T, E: Into<Report>>(f: impl FnOnce() -> Result<T, E>) -> T {
        // @@Hack: we have to create a dummy source map here so that we can use it
        // to report errors in the case that the compiler fails to start up. After the
        // workspace is initiated, it is replaced with the real source map.
        let source_map = SourceMap::new();

        match f() {
            Ok(value) => value,
            Err(err) => emit_fatal_error(err, &source_map),
        }
    }
}

/// The [DefaultCompilerInterface] holds all the information and state of the
/// compiler instance. Each stage of the compiler contains a `State` type
/// parameter which the compiler stores so that incremental executions of the
/// compiler are possible.
pub struct Compiler {
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

    /// The codegen backend storage.
    pub codegen_storage: CodeGenStorage,

    /// Sources that have passed from the `expansion` stage of the compiler.
    /// @@Todo: Use bit-flags to represent which module has been
    /// expanded/desugared/semantically checked/type checked.
    pub expanded_sources: HashSet<SourceId>,

    /// Sources that have passed from the `desugaring` stage of the compiler.
    pub desugared_modules: HashSet<SourceId>,

    /// Modules that have already been semantically checked. This is needed in
    /// order to avoid re-checking modules on re-evaluations of a workspace.
    pub semantically_checked_modules: HashSet<SourceId>,

    /// Compiler IR storage. Stores all the IR that is created during the
    /// lowering stage, which is used for later stages during code generation.
    pub ir_storage: IrStorage,

    /// Storage for all of the [Layout]s that have been created
    /// for the IR. Additionally, this also stores a cache for
    /// the looking up resultant [Layout]s by the specific IR type
    /// ID.
    pub layout_storage: LayoutCtx,
}

impl Compiler {
    /// Create a new compiler session with the input and output streams being
    /// set as the standard error and standard output streams.
    pub fn new(settings: CompilerSettings) -> Result<Self, PipelineError> {
        let workspace = Workspace::new(&settings)?;

        Ok(Self::with(
            workspace,
            settings,
            || CompilerOutputStream::Stderr(std::io::stderr()),
            || CompilerOutputStream::Stdout(std::io::stdout()),
        ))
    }

    /// Create a new [DefaultCompilerInterface].
    pub fn with(
        workspace: Workspace,
        settings: CompilerSettings,
        error_stream: impl Fn() -> CompilerOutputStream + 'static,
        output_stream: impl Fn() -> CompilerOutputStream + 'static,
    ) -> Self {
        // We need at least 2 workers for the parsing loop in order so that the job
        // queue can run within a worker and any other jobs can run inside another
        // worker or workers.
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(settings.worker_count + 1)
            .thread_name(|id| format!("compiler-worker-{id}"))
            .build()
            .unwrap();

        let target = settings.target();

        // @@Fixme: ideally this error should be handled else-where
        let layout_info = target
            .parse_data_layout()
            .unwrap_or_else(|err| utils::emit_fatal_error(err, &workspace.source_map));

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
            codegen_storage: CodeGenStorage::new(),
            expanded_sources: HashSet::new(),
            desugared_modules: HashSet::new(),
            semantically_checked_modules: HashSet::new(),
        }
    }
}

impl DefaultCtxQuery for Compiler {}

impl CompilerInterface for Compiler {
    /// Get a reference to the error [CompilerOutputStream].
    fn error_stream(&self) -> CompilerOutputStream {
        (self.error_stream)()
    }

    /// Get a reference to the output [CompilerOutputStream].
    fn output_stream(&self) -> CompilerOutputStream {
        // @@Craziness: rust syntax failure (RSF) is causing the compiler to
        // think that the `output_stream` field is a function, so we have to
        // wrap it in parentheses to get around this.
        //
        // See:
        //
        // (This was generated by GitHub Copilot)
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

impl ParserCtxQuery for Compiler {
    fn data(&mut self) -> ParserCtx {
        ParserCtx { workspace: &mut self.workspace, pool: &self.pool }
    }
}

impl AstDesugaringCtxQuery for Compiler {
    fn data(&mut self) -> AstDesugaringCtx {
        AstDesugaringCtx { workspace: &mut self.workspace, pool: &self.pool }
    }
}

impl UntypedSemanticAnalysisCtxQuery for Compiler {
    fn data(&mut self) -> UntypedSemanticAnalysisCtx {
        UntypedSemanticAnalysisCtx { workspace: &mut self.workspace, pool: &self.pool }
    }
}

impl AstExpansionCtxQuery for Compiler {
    fn data(&mut self) -> AstExpansionCtx {
        let output_stream = self.output_stream();
        AstExpansionCtx {
            workspace: &mut self.workspace,
            settings: &self.settings,
            stdout: output_stream,
        }
    }
}

impl SemanticAnalysisCtxQuery for Compiler {
    fn data(&mut self) -> SemanticAnalysisCtx {
        SemanticAnalysisCtx {
            workspace: &mut self.workspace,
            semantic_storage: &mut self.semantic_storage,
            settings: &self.settings,
        }
    }
}

impl LoweringCtxQuery for Compiler {
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

impl BackendCtxQuery for Compiler {
    fn data(&mut self) -> BackendCtx {
        let output_stream = self.output_stream();

        BackendCtx {
            codegen_storage: &self.codegen_storage,
            workspace: &mut self.workspace,
            ir_storage: &self.ir_storage,
            layout_storage: &self.layout_storage,
            settings: &self.settings,
            stdout: output_stream,
            _pool: &self.pool,
        }
    }
}

impl LinkerCtxQuery for Compiler {
    fn data(&mut self) -> hash_link::LinkerCtx<'_> {
        let stdout = self.output_stream();

        LinkerCtx { workspace: &self.workspace, settings: &self.settings, stdout }
    }
}

/// A trait that represents all compiler stages, essentially a newtype to use
/// when declaring that the compiler interface must implement all stages in the
/// compiler pipeline.
pub trait DefaultCtxQuery:
    ParserCtxQuery
    + AstDesugaringCtxQuery
    + AstExpansionCtxQuery
    + UntypedSemanticAnalysisCtxQuery
    + SemanticAnalysisCtxQuery
    + LoweringCtxQuery
    + BackendCtxQuery
    + LinkerCtxQuery
{
}
