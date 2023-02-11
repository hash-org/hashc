//! The first pass of the typechecker, which discovers all definitions in
//! the AST and adds them to the stores.

use hash_ast::{
    ast::{self},
    visitor::AstVisitor,
};
use hash_tir::new::{environment::env::AccessToEnv, symbols::Symbol, utils::common::CommonUtils};
use hash_utils::state::LightState;

use self::defs::DefDiscoveryState;
use super::ast_utils::AstPass;
use crate::new::environment::tc_env::{AccessToTcEnv, TcEnv};

pub mod defs;
pub mod params;
pub mod visitor;

pub struct DiscoveryPass<'tc> {
    tc_env: &'tc TcEnv<'tc>,
    /// The name hint for the current definition.
    name_hint: LightState<Option<Symbol>>,
    /// Keeps track of which definitions have been seen, added, and we are
    /// currently inside.
    def_state: DefDiscoveryState,
}

impl AccessToEnv for DiscoveryPass<'_> {
    fn env(&self) -> &hash_tir::new::environment::env::Env {
        self.tc_env.env()
    }
}

impl<'tc> AccessToTcEnv for DiscoveryPass<'tc> {
    fn tc_env(&self) -> &'tc TcEnv<'tc> {
        self.tc_env
    }
}

impl<'tc> AstPass for DiscoveryPass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::new::diagnostics::error::SemanticResult<()> {
        self.visit_body_block(node)
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::SemanticResult<()> {
        self.visit_module(node)
    }
}

impl<'tc> DiscoveryPass<'tc> {
    pub fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        Self { tc_env, name_hint: LightState::new(None), def_state: DefDiscoveryState::new() }
    }

    /// Get the current definition discovery state
    fn def_state(&self) -> &DefDiscoveryState {
        &self.def_state
    }

    /// Take the currently set name hint, or create a new internal name.
    fn take_name_hint_or_create_internal_name(&self) -> Symbol {
        self.name_hint.take().unwrap_or_else(|| self.new_fresh_symbol())
    }
}
