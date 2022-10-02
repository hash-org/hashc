//! Hash Compiler pipeline traits. This file contains implementable interfaces
//! that are used by the pipeline to run various stages that transform the
//! provided sources into runnable/executable code.

use hash_ast::node_map::{InteractiveBlock, ModuleEntry, NodeMap};
use hash_reporting::report::Report;
use hash_source::{InteractiveId, ModuleId, ModuleKind, SourceId, SourceMap};

use crate::{
    settings::{CompilerSettings, CompilerStageKind},
    workspace::Workspace,
};

pub type CompilerResult<T> = Result<T, Vec<Report>>;

/// [CompilerStage] represents an abstract stage within the compiler pipeline.
/// Each stage has an associated [CompilerStageKind] which can be used by
/// the pipeline which stages to run.
pub trait CompilerStage<StageCtx> {
    /// Run the stage, with an initial `entry_point` module. For most
    /// stages this is irrelevant since the module dependency graph
    /// is not relevant for the stage.
    fn run_stage(&mut self, entry_point: SourceId, stage_data: &mut StageCtx)
        -> CompilerResult<()>;

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
    fn cleanup(&self, _entry_point: SourceId, _stage_data: &mut StageCtx) {}

    /// This function is used to to return the `stage` kind of
    /// this [CompilerStage].
    fn stage_kind(&self) -> CompilerStageKind;
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
    /// Get the [CompilerSettings]. The settings represent any commandline
    /// arguments that were passed into the [CompilerSession].
    fn settings(&self) -> &CompilerSettings;

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
    fn add_module(&mut self, contents: String, module: ModuleEntry, kind: ModuleKind) -> ModuleId {
        self.workspace_mut().add_module(contents, module, kind)
    }

    /// Add a [InteractiveBlock] via the [Workspace].
    fn add_interactive_block(&mut self, input: String, block: InteractiveBlock) -> InteractiveId {
        self.workspace_mut().add_interactive_block(input, block)
    }
}
