use hash_ast::{
    ast::{AstNodeRef, BodyBlock, Module, OwnsAstNode},
    node_map::SourceRef,
};

use crate::{diagnostics::error::SemanticResult, environment::sem_env::AccessToSemEnv};

pub trait AstPass: AccessToSemEnv {
    /// Some passes may want to return a value
    type PassOutput;

    /// Called when the pass is run on an interactive source
    fn pass_interactive(&self, node: AstNodeRef<BodyBlock>) -> SemanticResult<Self::PassOutput>;

    /// Called when the pass is run on a module source
    fn pass_module(&self, node: AstNodeRef<Module>) -> SemanticResult<Self::PassOutput>;

    /// Called before the pass starts, returns `Some(output)` if the pass should
    /// not go ahead
    fn pre_pass(&self) -> SemanticResult<Option<Self::PassOutput>> {
        Ok(None)
    }

    /// Called after the pass has finished
    fn post_pass(&self, _: &Self::PassOutput) -> SemanticResult<()> {
        Ok(())
    }

    /// Run the pass on the current source
    fn pass_source(&self) -> SemanticResult<Self::PassOutput> {
        if let Some(output) = self.pre_pass()? {
            Ok(output)
        } else {
            let source = self.node_map().get_source(self.current_source_info().source_id());
            let output = match source {
                SourceRef::Interactive(interactive_source) => {
                    self.pass_interactive(interactive_source.node_ref())?
                }
                SourceRef::Module(module_source) => self.pass_module(module_source.node_ref())?,
            };
            self.post_pass(&output)?;
            Ok(output)
        }
    }
}

pub trait AstUtils: AccessToSemEnv {}

impl<T: AccessToSemEnv> AstUtils for T {}
