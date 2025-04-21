//! The second pass of the typechecker, which resolves all symbols to their
//! referenced bindings, and creates the initial term/type/pattern structure
//! ready for further elaboration.
//!
//! Any scoping errors are reported here.

use derive_more::Deref;
use hash_ast::ast;
use hash_source::SourceId;

use self::{
    pat_binds::PatBindsChecker,
    scoping::{ContextKind, Scoping},
};
use super::{analysis_pass::AnalysisPass, ast_info::AstInfo};
use crate::{diagnostics::definitions::SemanticResult, env::SemanticEnv, progress::AnalysisStage};

pub mod defs;
pub mod directives;
pub mod exprs;
pub mod params;
pub(crate) mod pat_binds;
pub mod paths;
pub mod pats;
pub mod scoping;
pub mod tys;

/// The second pass of the typechecker, which resolves all symbols to their
/// referenced bindings.
#[derive(Deref)]
pub struct ResolutionPass<'env, E: SemanticEnv> {
    #[deref]
    env: &'env E,
    /// Tools for entering scopes and looking up symbols by name in them.
    scoping: Scoping<'env, E>,
    /// AST info from discovery pass.
    ast_info: &'env AstInfo,
}

impl<E: SemanticEnv> AnalysisPass for ResolutionPass<'_, E> {
    type Env = E;
    fn env(&self) -> &Self::Env {
        self.env
    }

    type PassOutput = ();

    fn pass_interactive(
        &self,
        _source: SourceId,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> SemanticResult<()> {
        let root_mod = self.root_mod();
        self.scoping().add_scope(ContextKind::Environment);
        self.scoping().add_mod_members(root_mod);

        // If the prelude is set, add its members to the root module.
        if let Some(prelude) = self.prelude_mod().get() {
            self.scoping().add_mod_members(*prelude);
        }

        let term_id = self.make_term_from_ast_body_block(node)?;
        self.ast_info.terms().insert(node.id(), term_id);
        Ok(())
    }

    fn pass_module(
        &self,
        source: SourceId,
        node: ast::AstNodeRef<ast::Module>,
    ) -> SemanticResult<()> {
        let root_mod = self.root_mod();
        self.scoping().add_scope(ContextKind::Environment);
        self.scoping().add_mod_members(root_mod);

        // If the prelude is set, add its members to the root module.
        if let Some(prelude) = self.prelude_mod().get() {
            self.scoping().add_mod_members(*prelude);
        }

        let mod_def_id = self.resolve_ast_module_inner_terms(node)?;

        if source.is_prelude() {
            self.prelude_mod().set(mod_def_id).expect("Tried to set prelude twice");
        }

        Ok(())
    }

    fn pre_pass(&self, source: SourceId) -> SemanticResult<Option<()>> {
        if self.get_current_progress(source) < AnalysisStage::Resolution {
            self.set_current_progress(source, AnalysisStage::Resolution);
            Ok(None)
        } else {
            Ok(Some(()))
        }
    }
}

impl<'env, E: SemanticEnv + 'env> ResolutionPass<'env, E> {
    pub(crate) fn new(env: &'env E, ast_info: &'env AstInfo) -> Self {
        Self { env, scoping: Scoping::new(env, ast_info), ast_info }
    }

    /// Get a new pattern binder checker.
    fn pat_binds_validator(&self) -> PatBindsChecker<E> {
        PatBindsChecker::new(self.env)
    }

    /// Get access to the current scoping state and operations.
    fn scoping(&self) -> &Scoping<E> {
        &self.scoping
    }
}
