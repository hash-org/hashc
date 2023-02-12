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
use hash_tir::new::environment::env::AccessToEnv;

use self::scoping::{ContextKind, Scoping};
use super::ast_utils::AstPass;
use crate::new::{
    environment::tc_env::{AccessToTcEnv, TcEnv},
    ops::bootstrap::BootstrapOps,
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
    tc_env: &'tc TcEnv<'tc>,
    /// Tools for entering scopes and looking up symbols by name in them.
    scoping: Scoping<'tc>,
}

impl AccessToIntrinsics for ResolutionPass<'_> {
    fn intrinsics(&self) -> &DefinedIntrinsics {
        self.tc_env.intrinsics()
    }
}

impl AccessToPrimitives for ResolutionPass<'_> {
    fn primitives(&self) -> &DefinedPrimitives {
        self.tc_env.primitives()
    }
}

impl AccessToEnv for ResolutionPass<'_> {
    fn env(&self) -> &hash_tir::new::environment::env::Env {
        self.tc_env.env()
    }
}

impl AccessToTcEnv for ResolutionPass<'_> {
    fn tc_env(&self) -> &TcEnv<'_> {
        self.tc_env
    }
}

impl<'tc> AstPass for ResolutionPass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::new::diagnostics::error::SemanticResult<()> {
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

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::SemanticResult<()> {
        let root_mod = self.bootstrap();
        self.scoping().add_scope(root_mod.into(), ContextKind::Environment);
        self.scoping().add_mod_members(root_mod);

        // If the prelude is set, add its members to the root module.
        if let Some(prelude) = self.prelude_or_unset().get() {
            self.scoping().add_mod_members(*prelude);
        }

        let mod_def_id = self.resolve_ast_module_inner_terms(node)?;

        if let Some(ModuleKind::Prelude) =
            self.source_map().module_kind_by_id(self.current_source_info().source_id)
        {
            let _ = self.prelude_or_unset().set(mod_def_id);
        }

        Ok(())
    }
}

impl<'tc> ResolutionPass<'tc> {
    pub(crate) fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        Self { tc_env, scoping: Scoping::new(tc_env) }
    }

    /// Get access to the current scoping state and operations.
    fn scoping(&self) -> &Scoping {
        &self.scoping
    }
}
