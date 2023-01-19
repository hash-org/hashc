//! The second pass of the typechecker, which resolves all symbols to their
//! referenced bindings, and creates the initial term/type/pattern structure
//! ready for further elaboration.
//!
//! Any scoping errors are reported here.

use hash_ast::ast::{self};

use self::scoping::{ContextKind, Scoping};
use super::ast_utils::{AstPass, AstUtils};
use crate::{
    impl_access_to_tc_env,
    new::{environment::tc_env::TcEnv, ops::AccessToOps},
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

impl_access_to_tc_env!(ResolutionPass<'tc>);

impl<'tc> AstPass for ResolutionPass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
        // @@Todo: add intrinsics to the environment
        let (prim_mod, _) = self.bootstrap_ops().bootstrap();
        self.scoping().add_scope(prim_mod.into(), ContextKind::Environment);
        let _ = self.make_term_from_ast_body_block(node)?;
        Ok(())
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
        let (prim_mod, _) = self.bootstrap_ops().bootstrap();
        self.scoping().add_scope(prim_mod.into(), ContextKind::Environment);
        let _ = self.resolve_ast_module_inner_terms(node)?;
        Ok(())
    }
}

impl AstUtils for ResolutionPass<'_> {}

impl<'tc> ResolutionPass<'tc> {
    pub(crate) fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        Self { tc_env, scoping: Scoping::new(tc_env) }
    }

    /// Get access to the current scoping state and operations.
    fn scoping(&self) -> &Scoping {
        &self.scoping
    }
}
