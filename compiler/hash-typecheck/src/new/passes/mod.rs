use hash_ast::{ast::OwnsAstNode, node_map::SourceRef, visitor::AstVisitor};

use self::symbol_resolving::SymbolResolvingPass;
use super::data::env::{AccessToTcEnv, TcEnv};
use crate::impl_access_to_tc_env;

pub mod symbol_resolving;

pub struct TcVisitor<'tc> {
    env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(TcVisitor<'tc>);

impl<'tc> TcVisitor<'tc> {
    pub fn new(env: &'tc TcEnv<'tc>) -> Self {
        TcVisitor { env }
    }

    /// Visits the source passed in as an argument to [Self::new_in_source], and
    /// returns the term of the module that corresponds to the source.
    pub fn visit_source(&self) {
        let source = self.node_map().get_source(self.current_source_info().source_id);

        let symbol_resolving_pass = SymbolResolvingPass::new(self.env);

        let result = match source {
            SourceRef::Interactive(interactive_source) => {
                symbol_resolving_pass.visit_body_block(interactive_source.node_ref())
            }
            SourceRef::Module(module_source) => {
                symbol_resolving_pass.visit_module(module_source.node_ref())
            }
        };

        if let Err(err) = result {
            self.diagnostics_store().errors.borrow_mut().push(err);
        }
    }
}
