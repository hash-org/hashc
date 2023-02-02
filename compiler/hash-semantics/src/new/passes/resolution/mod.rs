//! The second pass of the typechecker, which resolves all symbols to their
//! referenced bindings, and creates the initial term/type/pattern structure
//! ready for further elaboration.
//!
//! Any scoping errors are reported here.

use hash_ast::ast::{self};
use hash_intrinsics::primitives::{AccessToPrimitives, DefinedPrimitives};
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
        // @@Todo: add intrinsics to the environment
        let (prim_mod, _) = self.bootstrap();
        self.scoping().add_scope(prim_mod.into(), ContextKind::Environment);
        self.scoping().add_mod_members(prim_mod);
        let term_id = self.make_term_from_ast_body_block(node)?;
        self.ast_info().terms().insert(node.id(), term_id);
        Ok(())
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::SemanticResult<()> {
        let (prim_mod, _) = self.bootstrap();
        self.scoping().add_scope(prim_mod.into(), ContextKind::Environment);
        self.scoping().add_mod_members(prim_mod);
        let _ = self.resolve_ast_module_inner_terms(node)?;
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
