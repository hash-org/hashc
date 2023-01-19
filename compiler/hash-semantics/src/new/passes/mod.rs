use self::{ast_utils::AstPass, discovery::DiscoveryPass, resolution::ResolutionPass};
use super::environment::tc_env::{AccessToTcEnv, TcEnv};
use crate::impl_access_to_tc_env;

pub mod ast_utils;
pub mod discovery;
pub mod resolution;

/// The base TC visitor, which runs each typechecking pass in order on the AST.
pub struct TcVisitor<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(TcVisitor<'tc>);

impl<'tc> TcVisitor<'tc> {
    pub fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        TcVisitor { tc_env }
    }

    /// Visits the source passed in as an argument to [Self::new_in_source]
    pub fn visit_source(&self) {
        DiscoveryPass::new(self.tc_env).pass_source();
        if self.diagnostics().has_errors() {
            return;
        }

        ResolutionPass::new(self.tc_env).pass_source();
    }
}