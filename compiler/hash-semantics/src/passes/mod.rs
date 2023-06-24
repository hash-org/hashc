use hash_tir::environment::env::{AccessToEnv, Env};

use self::{
    ast_utils::AstPass, discovery::DiscoveryPass, evaluation::EvaluationPass,
    inference::InferencePass, resolution::ResolutionPass,
};
use super::environment::sem_env::{AccessToSemEnv, SemEnv};
use crate::diagnostics::error::SemanticResult;

pub mod ast_utils;
pub mod discovery;
pub mod evaluation;
pub mod inference;
pub mod resolution;

/// The base semantic analysis visitor, which runs each analysis pass in
/// order on the AST.
pub struct Visitor<'tc> {
    sem_env: &'tc SemEnv<'tc>,
}

impl AccessToEnv for Visitor<'_> {
    fn env(&self) -> &Env {
        self.sem_env.env()
    }
}

impl AccessToSemEnv for Visitor<'_> {
    fn sem_env(&self) -> &SemEnv<'_> {
        self.sem_env
    }
}

impl<'tc> Visitor<'tc> {
    pub fn new(sem_env: &'tc SemEnv<'tc>) -> Self {
        Visitor { sem_env }
    }

    /// Visits the source passed in as an argument to [Self::new_in_source]
    pub fn visit_source(&self) -> SemanticResult<()> {
        // Discover all definitions in the source.
        DiscoveryPass::new(self.sem_env).pass_source()?;

        // Resolve all symbols in the source and create TIR terms.
        ResolutionPass::new(self.sem_env).pass_source()?;

        // Infer all types in the source.
        //
        // This needs to be run twice, once to infer the headers of the
        // definitions, and once to infer their bodies.
        InferencePass::new(self.sem_env).pass_source()?;
        InferencePass::new(self.sem_env).pass_source()?;

        // Potentially evaluate terms
        EvaluationPass::new(self.sem_env).pass_source()?;

        Ok(())
    }
}
