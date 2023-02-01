//! Utilities for creating parameters and arguments during discovery.
use hash_ast::ast::{self};
use hash_tir::new::{environment::env::AccessToEnv, params::ParamsId, utils::AccessToUtils};

use super::DiscoveryPass;
use crate::new::{environment::tc_env::AccessToTcEnv, passes::ast_utils::AstUtils};

impl<'tc> DiscoveryPass<'tc> {
    /// Create a parameter list from the given AST generic parameter list, where
    /// the type of each parameter is a hole.
    pub(super) fn create_hole_params_from<T>(
        &self,
        params: &ast::AstNodes<T>,
        name: impl Fn(&T) -> &Option<ast::AstNode<ast::Name>>,
    ) -> ParamsId {
        let params_id = self.param_utils().create_hole_params(
            params.iter().map(|param| self.create_symbol_from_ast_name(name(param))),
        );
        self.stores()
            .location()
            .add_locations_to_targets(params_id, |i| Some(self.source_location(params[i].span())));

        for (i, param) in params.iter().enumerate() {
            self.ast_info().params().insert(param.id(), (params_id, i));
        }

        params_id
    }

    /// Create a parameter list from the given AST parameter list, where the
    /// type of each parameter is a hole.
    pub(super) fn create_hole_params(&self, params: &ast::AstNodes<ast::Param>) -> ParamsId {
        self.create_hole_params_from(params, |param| &param.name)
    }
}
