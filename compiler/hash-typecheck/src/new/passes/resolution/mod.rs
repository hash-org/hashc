//! The second pass of the typechecker, which resolves all symbols to their
//! referenced bindings.
//!
//! Any scoping errors are reported here.

use std::fmt;

use hash_ast::{
    ast::{self},
    visitor::AstVisitor,
};
use hash_types::new::{environment::env::AccessToEnv, locations::LocationTarget};
use hash_utils::state::LightState;

use self::{paths::*, scoping::Scoping};
use super::ast_utils::{AstPass, AstUtils};
use crate::{
    impl_access_to_tc_env,
    new::{
        environment::tc_env::{TcEnv, WithTcEnv},
        ops::{common::CommonOps, AccessToOps},
    },
};

pub mod exprs;
pub mod params;
pub mod paths;
pub mod pats;
pub mod scoping;
pub mod tys;
pub mod visitor;

/// The current expression kind we are in.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum InExpr {
    /// We are in a type expression.
    Ty,
    /// We are in a value expression.
    Value,
    /// We are in a pattern.
    Pat,
}

/// The kind of context we are in.
///
/// Either we are trying to resolve a symbol in the environment, or we are
/// trying to resolve a symbol through access of another term.
#[derive(Copy, Clone, Debug)]
pub enum ContextKind {
    /// An access context, where we are trying to resolve a symbol through
    /// access of another term.
    ///
    /// The tuple contains the identifier accessing from and the location target
    /// of the definition .
    Access(NonTerminalResolvedPathComponent, LocationTarget),
    /// Just the current scope.
    Environment,
}

impl fmt::Display for WithTcEnv<'_, &ContextKind> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            ContextKind::Access(non_terminal, _loc) => {
                write!(f, "{}", self.tc_env().with(non_terminal))
            }
            ContextKind::Environment => write!(f, "the current scope"),
        }
    }
}

/// The second pass of the typechecker, which resolves all symbols to their
/// referenced bindings.
pub struct SymbolResolutionPass<'tc> {
    tc_env: &'tc TcEnv<'tc>,
    in_expr: LightState<InExpr>,
    scoping: Scoping<'tc>,
}

impl_access_to_tc_env!(SymbolResolutionPass<'tc>);

impl<'tc> AstPass for SymbolResolutionPass<'tc> {
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

impl AstUtils for SymbolResolutionPass<'_> {}

impl<'tc> SymbolResolutionPass<'tc> {
    pub fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        Self { tc_env, in_expr: LightState::new(InExpr::Value), scoping: Scoping::new(tc_env) }
    }

    /// Get access to the current scoping state and operations.
    pub fn scoping(&self) -> &Scoping {
        &self.scoping
    }
}
