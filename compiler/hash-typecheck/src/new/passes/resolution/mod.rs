//! The second pass of the typechecker, which resolves all symbols to their
//! referenced bindings, and creates the initial term/type/pattern structure
//! ready for further elaboration.
//!
//! Any scoping errors are reported here.

use hash_ast::{
    ast::{self},
    visitor::AstVisitor,
};
use hash_types::new::environment::env::AccessToEnv;
use hash_utils::state::LightState;

use self::scoping::Scoping;
use super::ast_utils::{AstPass, AstUtils};
use crate::{
    impl_access_to_tc_env,
    new::{
        environment::tc_env::TcEnv,
        ops::{common::CommonOps, AccessToOps},
    },
};

pub mod defs;
pub mod exprs;
pub mod params;
pub mod paths;
pub mod pats;
pub mod scoping;
pub mod tys;
pub mod visitor;

// @@Todo: remove
/// The current expression kind we are in.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum InExpr {
    // Not in an expr, but in some kind of definition
    Def,
    /// We are in a type expression.
    Ty,
    /// We are in a value expression.
    Value,
    /// We are in a pattern.
    Pat,
}

/// The second pass of the typechecker, which resolves all symbols to their
/// referenced bindings.
pub struct ResolutionPass<'tc> {
    tc_env: &'tc TcEnv<'tc>,
    /// Keeps track of the current state of the visitor in terms of if it is
    /// currently traversing an expression/pattern/type or not.
    in_expr: LightState<InExpr>,
    /// Tools for entering scopes and looking up symbols by name in them.
    scoping: Scoping<'tc>,
}

impl_access_to_tc_env!(ResolutionPass<'tc>);

impl<'tc> AstPass for ResolutionPass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
        self.bootstrap_ops().bootstrap(|| self.visit_body_block(node))
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
        self.bootstrap_ops().bootstrap(|| {
            println!("{}", self.env().with(self.primitives().option()));
            self.visit_module(node)
        })
    }
}

impl AstUtils for ResolutionPass<'_> {}

impl<'tc> ResolutionPass<'tc> {
    pub(crate) fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        Self { tc_env, in_expr: LightState::new(InExpr::Def), scoping: Scoping::new(tc_env) }
    }

    /// Get access to the current scoping state and operations.
    fn scoping(&self) -> &Scoping {
        &self.scoping
    }
}
