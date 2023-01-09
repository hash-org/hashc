//! The first pass of the typechecker, which discovers all definitions in
//! the AST and adds them to the stores.
use hash_ast::{
    ast::{self},
    visitor::AstVisitor,
};
use hash_types::new::symbols::Symbol;
use hash_utils::state::LightState;

use self::defs::DefDiscoveryState;
use super::ast_utils::{AstPass, AstUtils};
use crate::{
    impl_access_to_tc_env,
    new::{environment::tc_env::TcEnv, ops::common::CommonOps},
};

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

impl AstUtils for DiscoveryPass<'_> {}

impl_access_to_tc_env!(DiscoveryPass<'tc>);

impl<'tc> AstPass for DiscoveryPass<'tc> {
    fn pass_interactive(
        &self,
        node: ast::AstNodeRef<ast::BodyBlock>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
        self.visit_body_block(node)
    }

    fn pass_module(
        &self,
        node: ast::AstNodeRef<ast::Module>,
    ) -> crate::new::diagnostics::error::TcResult<()> {
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

    /// Create a new symbol from the given optional AST node containing a name.
    ///
    /// If the AST node is `None`, a fresh symbol is created.
    fn create_symbol_from_ast_name(&self, ast_name: &Option<ast::AstNode<ast::Name>>) -> Symbol {
        match ast_name {
            Some(ast_name) => self.new_symbol(ast_name.ident),
            None => self.new_fresh_symbol(),
        }
    }

    /// Take the currently set name hint, or create a new internal name.
    fn take_name_hint_or_create_internal_name(&self) -> Symbol {
        self.name_hint.take().unwrap_or_else(|| self.new_fresh_symbol())
    }
}
