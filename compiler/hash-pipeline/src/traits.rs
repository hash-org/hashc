//! Hash Compiler pipeline traits. This file contains implementable interfaces
//! that are used by the pipeline to run various stages that transform the
//! provided sources into runnable/executable code.

use hash_reporting::report::Report;
use hash_source::SourceId;

use crate::{
    settings::{CompilerSettings, CompilerStageKind},
    sources::Workspace,
};

pub type CompilerResult<T> = Result<T, Vec<Report>>;

/// [CompilerStage] represents an abstract stage within the compiler pipeline.
/// Each stage has an associated [CompilerStageKind] which can be used by
/// the pipeline which stages to run.
pub trait CompilerStage<'pool> {
    /// Run the stage, with an initial `entry_point` module. For most
    /// stages this is irrelevant since the module dependency graph
    /// is not relevant for the stage.
    fn run_stage(
        &mut self,
        entry_point: SourceId,
        workspace: &mut Workspace,
        pool: &'pool rayon::ThreadPool,
    ) -> CompilerResult<()>;

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
    fn cleanup(
        &self,
        _entry_point: SourceId,
        _workspace: &mut Workspace,
        _settings: &CompilerSettings,
    ) {
    }

    /// This function is used to to return the `stage` kind of
    /// this [CompilerStage].
    fn stage_kind(&self) -> CompilerStageKind;
}
