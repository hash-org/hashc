//! The first pass of the typechecker, which discovers all definitions in
//! the AST and adds them to the stores.

use hash_ast::{
    ast::{self},
    visitor::AstVisitor,
};
use hash_tir::{environment::env::AccessToEnv, symbols::Symbol, utils::common::CommonUtils};
use hash_utils::state::LightState;

use self::defs::DefDiscoveryState;
use super::ast_utils::AstPass;
use crate::environment::sem_env::{AccessToSemEnv, SemEnv};

pub mod defs;
pub mod params;
pub mod visitor;

pub struct DiscoveryPass<'tc> {
    sem_env: &'tc SemEnv<'tc>,
    /// The name hint for the current definition.
    name_hint: LightState<Option<Symbol>>,
    /// Keeps track of which definitions have been seen, added, and we are
    /// currently inside.
    def_state: DefDiscoveryState,
}

impl AccessToEnv for DiscoveryPass<'_> {
    fn env(&self) -> &hash_tir::environment::env::Env {
        self.sem_env.env()
    }
}

impl<'tc> AccessToSemEnv for DiscoveryPass<'tc> {
    fn sem_env(&self) -> &'tc SemEnv<'tc> {
        self.sem_env
    }
}

impl<'tc> AstPass for DiscoveryPass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::diagnostics::error::SemanticResult<()> {
        self.visit_body_block(node)
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::diagnostics::error::SemanticResult<()> {
        self.visit_module(node)
    }
}

impl<'tc> DiscoveryPass<'tc> {
    pub fn new(sem_env: &'tc SemEnv<'tc>) -> Self {
        Self { sem_env, name_hint: LightState::new(None), def_state: DefDiscoveryState::new() }
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
