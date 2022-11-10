use hash_ast::{ast::OwnsAstNode, node_map::SourceRef, visitor::AstVisitorMutSelf};
use hash_types::new::environment::env::AccessToEnv;

use self::scope_discovery::ScopeDiscoveryPass;
use super::environment::tc_env::{AccessToTcEnv, TcEnv};
use crate::impl_access_to_tc_env;

pub mod scope_discovery;

/// The base TC visitor, which runs each typechecking pass in order on the AST.
pub struct TcVisitor<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(TcVisitor<'tc>);

impl<'tc> TcVisitor<'tc> {
    pub fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        TcVisitor { tc_env }
    }

    /// Visits the source passed in as an argument to [Self::new_in_source], and
    /// returns the term of the module that corresponds to the source.
    pub fn visit_source(&self) {
        let source = self.node_map().get_source(self.current_source_info().source_id);

        // First, we need to discover the scopes of the source.
        let mut scope_discovery = ScopeDiscoveryPass::new(self.tc_env());

        let result = match source {
            SourceRef::Interactive(interactive_source) => {
                scope_discovery.visit_body_block(interactive_source.node_ref())
            }
            SourceRef::Module(module_source) => {
                scope_discovery.visit_module(module_source.node_ref())
            }
        };

        // Record errors
        if let Err(err) = result {
            self.diagnostics_store().errors.borrow_mut().push(err);
        }
    }
}
