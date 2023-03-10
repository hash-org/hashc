//! The second pass of the typechecker, which resolves all symbols to their
//! referenced bindings, and creates the initial term/type/pattern structure
//! ready for further elaboration.
//!
//! Any scoping errors are reported here.

use hash_ast::ast::{self};
use hash_intrinsics::{
    intrinsics::{AccessToIntrinsics, DefinedIntrinsics},
    primitives::{AccessToPrimitives, DefinedPrimitives},
};
use hash_source::ModuleKind;
use hash_tir::environment::env::AccessToEnv;

use self::scoping::{ContextKind, Scoping};
use super::ast_utils::AstPass;
use crate::{
    diagnostics::error::SemanticResult,
    environment::{
        analysis_progress::AnalysisStage,
        sem_env::{AccessToSemEnv, SemEnv},
    },
    ops::{bootstrap::BootstrapOps, common::CommonOps},
};

pub mod defs;
pub mod exprs;
pub mod params;
pub mod paths;
pub mod pats;
pub mod scoping;
pub mod tys;

/// The second pass of the typechecker, which resolves all symbols to their
/// referenced bindings.
pub struct ResolutionPass<'tc> {
    sem_env: &'tc SemEnv<'tc>,
    /// Tools for entering scopes and looking up symbols by name in them.
    scoping: Scoping<'tc>,
}

impl AccessToIntrinsics for ResolutionPass<'_> {
    fn intrinsics(&self) -> &DefinedIntrinsics {
        self.sem_env.intrinsics()
    }
}

impl AccessToPrimitives for ResolutionPass<'_> {
    fn primitives(&self) -> &DefinedPrimitives {
        self.sem_env.primitives()
    }
}

impl AccessToEnv for ResolutionPass<'_> {
    fn env(&self) -> &hash_tir::environment::env::Env {
        self.sem_env.env()
    }
}

impl AccessToSemEnv for ResolutionPass<'_> {
    fn sem_env(&self) -> &SemEnv<'_> {
        self.sem_env
    }
}

impl<'tc> AstPass for ResolutionPass<'tc> {
    fn pass_interactive(&self, node: ast::AstNodeRef<ast::BodyBlock>) -> SemanticResult<()> {
        let root_mod = self.bootstrap();
        self.scoping().add_scope(root_mod.into(), ContextKind::Environment);
        self.scoping().add_mod_members(root_mod);

        // If the prelude is set, add its members to the root module.
        if let Some(prelude) = self.prelude_or_unset().get() {
            self.scoping().add_mod_members(*prelude);
        }

        let term_id = self.make_term_from_ast_body_block(node)?;
        self.ast_info().terms().insert(node.id(), term_id);
        Ok(())
    }

    fn pass_module(&self, node: ast::AstNodeRef<ast::Module>) -> SemanticResult<()> {
        let root_mod = self.bootstrap();
        self.scoping().add_scope(root_mod.into(), ContextKind::Environment);
        self.scoping().add_mod_members(root_mod);

        // If the prelude is set, add its members to the root module.
        if let Some(prelude) = self.prelude_or_unset().get() {
            self.scoping().add_mod_members(*prelude);
        }

        let mod_def_id = self.resolve_ast_module_inner_terms(node)?;

        if let Some(ModuleKind::Prelude) =
            self.source_map().module_kind_by_id(self.current_source_info().source_id())
        {
            let _ = self.prelude_or_unset().set(mod_def_id);
        }

        Ok(())
    }

    fn pre_pass(&self) -> SemanticResult<bool> {
        if self.get_current_progress() < AnalysisStage::Resolution {
            self.set_current_progress(AnalysisStage::Resolution);
            Ok(true)
        } else {
            Ok(false)
        }
    }
}

impl<'tc> ResolutionPass<'tc> {
    pub(crate) fn new(sem_env: &'tc SemEnv<'tc>) -> Self {
        Self { sem_env, scoping: Scoping::new(sem_env) }
    }

    /// Get access to the current scoping state and operations.
    fn scoping(&self) -> &Scoping {
        &self.scoping
    }
}
