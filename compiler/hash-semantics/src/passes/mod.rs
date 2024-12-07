use hash_source::SourceId;
use hash_utils::derive_more::{Constructor, Deref};

use self::{
    analysis_pass::AnalysisPass, ast_info::AstInfo, discovery::DiscoveryPass,
    evaluation::EvaluationPass, inference::InferencePass, resolution::ResolutionPass,
};
use crate::{diagnostics::definitions::SemanticResult, env::SemanticEnv};

pub mod analysis_pass;
pub mod ast_info;
pub mod discovery;
pub mod evaluation;
pub mod inference;
pub mod resolution;
pub mod tc_env_impl;

/// The base semantic analysis visitor, which runs each analysis pass in
/// order on the AST.
#[derive(Constructor, Deref)]
pub struct Analyser<'env, E: SemanticEnv> {
    env: &'env E,
}

impl<E: SemanticEnv> Analyser<'_, E> {
    /// Visits the source passed in as an argument to [Self::new_in_source]
    pub fn visit_source(&self, source: SourceId) -> SemanticResult<()> {
        // AST info for discovery and resolution passes.
        // @@Todo: refactor this to have each stage return its own AST info.
        let ast_info = AstInfo::new();

        // Discover all definitions in the source.
        DiscoveryPass::new(self.env, &ast_info).pass_source(source)?;

        // Resolve all symbols in the source and create TIR terms.
        ResolutionPass::new(self.env, &ast_info).pass_source(source)?;

        // Infer all types in the source.
        //
        // This needs to be run twice, once to infer the headers of the
        // definitions, and once to infer their bodies.
        InferencePass::new(self.env, &ast_info).pass_source(source)?;
        InferencePass::new(self.env, &ast_info).pass_source(source)?;

        // Potentially evaluate terms
        EvaluationPass::new(self.env, &ast_info).pass_source(source)?;

        Ok(())
    }
}
