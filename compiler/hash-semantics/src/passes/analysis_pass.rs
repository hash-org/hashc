use hash_ast::{
    ast::{AstNodeRef, BodyBlock, Module, OwnsAstNode},
    node_map::{HasNodeMap, SourceRef},
};
use hash_source::SourceId;

use crate::{diagnostics::definitions::SemanticResult, env::SemanticEnv, progress::AnalysisStage};

pub trait AnalysisPass {
    type Env: SemanticEnv;
    fn env(&self) -> &Self::Env;

    /// Some passes may want to return a value
    type PassOutput;

    /// Called when the pass is run on an interactive source
    fn pass_interactive(
        &self,
        source: SourceId,
        node: AstNodeRef<BodyBlock>,
    ) -> SemanticResult<Self::PassOutput>;

    /// Called when the pass is run on a module source
    fn pass_module(
        &self,
        source: SourceId,
        node: AstNodeRef<Module>,
    ) -> SemanticResult<Self::PassOutput>;

    /// Called before the pass starts, returns `Some(output)` if the pass should
    /// not go ahead
    fn pre_pass(&self, _: SourceId) -> SemanticResult<Option<Self::PassOutput>> {
        Ok(None)
    }

    /// Called after the pass has finished
    fn post_pass(&self, _: SourceId, _: &Self::PassOutput) -> SemanticResult<()> {
        Ok(())
    }

    /// Set the progress of analysis for the current source.
    fn set_current_progress(&self, source: SourceId, stage: AnalysisStage) {
        self.env().storage().progress.set(source, stage);
    }

    /// Get the progress of analysis for the current source.
    fn get_current_progress(&self, source: SourceId) -> AnalysisStage {
        self.env().storage().progress.get(source)
    }

    /// Run the pass on the given source
    fn pass_source(&self, source: SourceId) -> SemanticResult<Self::PassOutput> {
        if let Some(output) = self.pre_pass(source)? {
            Ok(output)
        } else {
            let source_ref = self.env().node_map().get_source(source);
            let output = match source_ref {
                SourceRef::Interactive(interactive_source) => {
                    self.pass_interactive(source, interactive_source.node_ref())?
                }
                SourceRef::Module(module_source) => {
                    self.pass_module(source, module_source.node_ref())?
                }
            };
            self.post_pass(source, &output)?;
            Ok(output)
        }
    }
}
