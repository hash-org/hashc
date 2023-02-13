use hash_reporting::diagnostic::Diagnostics;
use hash_tir::environment::env::AccessToEnv;

use self::{
    ast_utils::AstPass, discovery::DiscoveryPass, inference::InferencePass,
    resolution::ResolutionPass,
};
use super::environment::tc_env::{AccessToTcEnv, TcEnv};

pub mod ast_utils;
pub mod discovery;
pub mod inference;
pub mod resolution;

/// The base TC visitor, which runs each typechecking pass in order on the AST.
pub struct TcVisitor<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl AccessToEnv for TcVisitor<'_> {
    fn env(&self) -> &hash_tir::environment::env::Env {
        self.tc_env.env()
    }
}

impl AccessToTcEnv for TcVisitor<'_> {
    fn tc_env(&self) -> &TcEnv<'_> {
        self.tc_env
    }
}

impl<'tc> TcVisitor<'tc> {
    pub fn new(tc_env: &'tc TcEnv<'tc>) -> Self {
        TcVisitor { tc_env }
    }

    /// Visits the source passed in as an argument to [Self::new_in_source]
    pub fn visit_source(&self) {
        self.context().clear_all();

        DiscoveryPass::new(self.tc_env).pass_source();
        if self.diagnostics().has_errors() {
            return;
        }

        ResolutionPass::new(self.tc_env).pass_source();
        if self.diagnostics().has_errors() {
            return;
        }

        InferencePass::new(self.tc_env).pass_source();
    }
}
