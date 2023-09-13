use hash_source::SourceId;
use hash_utils::derive_more::{Constructor, Deref};

use self::{ast_info::AstInfo, ast_utils::AstPass, discovery::DiscoveryPass};
use crate::{diagnostics::definitions::SemanticResult, env::SemanticEnv};

pub mod ast_info;
pub mod ast_utils;
pub mod discovery;
// @@nocheckin
// pub mod evaluation;
// pub mod inference;
// pub mod resolution;

/// The base semantic analysis visitor, which runs each analysis pass in
/// order on the AST.
#[derive(Constructor, Deref)]
pub struct Analyser<'env, E: SemanticEnv> {
    env: &'env E,
}

impl<'env, E: SemanticEnv> Analyser<'env, E> {
    /// Visits the source passed in as an argument to [Self::new_in_source]
    pub fn visit_source(&self, source: SourceId) -> SemanticResult<()> {
        // AST info for discovery and resolution passes.
        let ast_info = AstInfo::new();

        // Discover all definitions in the source.
        DiscoveryPass::new(self.env, &ast_info, source).pass_source(source)?;

        // // Resolve all symbols in the source and create TIR terms.
        // ResolutionPass::new(self.sem_env).pass_source()?;

        // // Infer all types in the source.
        // //
        // // This needs to be run twice, once to infer the headers of the
        // // definitions, and once to infer their bodies.
        // InferencePass::new(self.sem_env).pass_source()?;
        // InferencePass::new(self.sem_env).pass_source()?;

        // // Potentially evaluate terms
        // EvaluationPass::new(self.sem_env).pass_source()?;

        Ok(())
    }
}
