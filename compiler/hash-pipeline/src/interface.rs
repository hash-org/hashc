//! Hash Compiler pipeline traits. This file contains implementable interfaces
//! that are used by the pipeline to run various stages that transform the
//! provided sources into runnable/executable code.

use std::{
    sync::{Arc, Mutex},
    time::Duration,
};

use hash_ast::node_map::{InteractiveBlock, ModuleEntry, NodeMap};
use hash_reporting::report::Report;
use hash_source::{ModuleKind, SourceId, SourceMap};

use crate::{
    settings::{CompilerSettings, CompilerStageKind},
    workspace::Workspace,
};

pub type CompilerResult<T> = Result<T, Vec<Report>>;

/// A [StageMetrics] is a collection of timings for each section of a stage.
#[derive(Default, Debug, Clone)]
pub struct StageMetrics {
    /// The collected timings for each section of the stage.
    pub timings: Vec<(&'static str, Duration)>,
}

impl StageMetrics {
    /// Create an iterator over the collected timings.
    pub fn iter(&self) -> impl Iterator<Item = (&'static str, Duration)> + '_ {
        self.timings.iter().cloned()
    }
}

/// [CompilerStage] represents an abstract stage within the compiler pipeline.
/// Each stage has an associated [CompilerStageKind] which can be used by
/// the pipeline which stages to run.
pub trait CompilerStage<StageCtx> {
    /// Run the stage, with an initial `entry_point` module. For most
    /// stages this is irrelevant since the module dependency graph
    /// is not relevant for the stage.
    fn run(&mut self, entry_point: SourceId, stage_data: &mut StageCtx) -> CompilerResult<()>;

    /// A function that is invoked after the stage completes successfully, this
    /// might be needed to perform some additional operations when the stage
    /// has completed.
    ///
    /// An example of this use case might be for the parser. The parser stage
    /// checks whether the `--dump-ast` flag has been set within the
    /// compiler settings, if the flag is specified, then the compiler must
    /// emit the parsed AST. The parser does this by checking this condition
    /// and then invoking a function to emit all of the ASTs for each module
    /// within the workspace.
    fn cleanup(&mut self, _entry_point: SourceId, _stage_data: &mut StageCtx) {}

    /// Ask the stage for any collected metrics that it has collected during
    /// it's execution.
    ///
    /// By default, there are no collected metrics.
    fn metrics(&self) -> StageMetrics {
        StageMetrics::default()
    }

    /// This function is used to "reset" any collected metrics such that
    /// the stage can run.
    fn reset_metrics(&mut self) {}

    /// This function is used to to return the `stage` kind of
    /// this [CompilerStage].
    fn kind(&self) -> CompilerStageKind;
}

/// A [CompilerOutputStream] is used to specify where the output of the compiler
/// should be written to. This is used by the [CompilerInterface] to provide
/// the pipeline with the necessary information to write to the correct stream.
#[derive(Debug)]
pub enum CompilerOutputStream {
    /// A [CompilerOutputStream] that points to the `stdout` stream.
    Stdout(std::io::Stdout),

    /// A [CompilerOutputStream] that points to the `stderr` stream.
    Stderr(std::io::Stderr),

    /// A [CompilerOutputStream] that is backed by a [Mutex] and a [Vec].
    Owned(Arc<Mutex<Vec<u8>>>),
}

impl Clone for CompilerOutputStream {
    fn clone(&self) -> Self {
        match self {
            CompilerOutputStream::Stdout(_) => CompilerOutputStream::Stdout(std::io::stdout()),
            CompilerOutputStream::Stderr(_) => CompilerOutputStream::Stderr(std::io::stderr()),
            CompilerOutputStream::Owned(stream) => CompilerOutputStream::Owned(stream.clone()),
        }
    }
}

impl std::io::Write for CompilerOutputStream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self {
            CompilerOutputStream::Stdout(stream) => stream.write(buf),
            CompilerOutputStream::Stderr(stream) => stream.write(buf),
            CompilerOutputStream::Owned(stream) => {
                let mut stream = stream.lock().unwrap();
                stream.extend_from_slice(buf);
                Ok(buf.len())
            }
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match self {
            CompilerOutputStream::Stdout(stream) => stream.flush(),
            CompilerOutputStream::Stderr(stream) => stream.flush(),
            CompilerOutputStream::Owned(_) => Ok(()),
        }
    }
}

/// The [CompilerInterface] serves as an interface between the created compiler
/// session which is used by the pipeline itself and any specified
/// [CompilerStage]s which are currently present within the pipeline.
///
/// This interface is needed to provide the pipeline with the necessary
/// information for it to perform it's operations. Ultimately, the
/// [CompilerInterface] is just a wrapper around the `CompilerSession` struct
/// which is defined in `hash-session`.
pub trait CompilerInterface {
    /// Get a reference to the error [CompilerOutputStream].
    fn error_stream(&self) -> CompilerOutputStream;

    /// Get a reference to the output [CompilerOutputStream].
    fn output_stream(&self) -> CompilerOutputStream;

    /// Get the [CompilerSettings].
    fn settings(&self) -> &CompilerSettings;

    /// Get a mutable reference to the current [CompilerSettings].
    fn settings_mut(&mut self) -> &mut CompilerSettings;

    /// Check if the context has accumulated any errors.
    fn has_errors(&self) -> bool {
        self.diagnostics().iter().any(|report| report.is_error())
    }

    /// Get the current [Report]s that have been collected by the compiler.
    fn diagnostics(&self) -> &[Report];

    /// Get a mutable reference to the current [Report]s that have been
    /// collected.
    fn diagnostics_mut(&mut self) -> &mut Vec<Report>;

    /// Get the current [Workspace]. The workspace contains all the sources and
    /// modules that the compiler has collected.
    fn workspace(&self) -> &Workspace;

    /// Get a mutable reference to the current [Workspace].
    fn workspace_mut(&mut self) -> &mut Workspace;

    /// Get a reference to the current [NodeMap].
    fn node_map(&self) -> &NodeMap;

    /// Get a reference to the current [SourceMap].
    fn source_map(&self) -> &SourceMap;

    /// Add a [ModuleEntry] via the [Workspace].
    fn add_module(&mut self, contents: String, module: ModuleEntry, kind: ModuleKind) -> SourceId {
        self.workspace_mut().add_module(contents, module, kind)
    }

    /// Add a [InteractiveBlock] via the [Workspace].
    fn add_interactive_block(&mut self, input: String, block: InteractiveBlock) -> SourceId {
        self.workspace_mut().add_interactive_block(input, block)
    }
}
