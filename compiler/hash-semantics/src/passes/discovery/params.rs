//! Utilities for creating parameters and arguments during discovery.
use hash_ast::ast::{self};
use hash_tir::{
    environment::env::AccessToEnv,
    params::{ParamId, ParamIndex, ParamsId},
    utils::AccessToUtils,
};

use super::DiscoveryPass;
use crate::{ops::common::CommonOps, passes::ast_utils::AstUtils};

impl<'tc> DiscoveryPass<'tc> {
    /// Create a parameter list from the given AST generic parameter list, where
    /// the type of each parameter is a hole.
    pub(super) fn create_hole_params_from<T>(
        &self,
        params: &ast::AstNodes<T>,
        name: impl Fn(&T) -> &Option<ast::AstNode<ast::Name>>,
    ) -> ParamsId {
        let params_id = self.param_utils().create_hole_params(
            params
                .iter()
                .enumerate()
                .map(|(i, param)| match name(param) {
                    Some(name) => ParamIndex::Name(name.ident),
                    None => ParamIndex::Position(i),
                })
                .map(|index| index.into_symbol()),
        );
        self.stores()
            .location()
            .add_locations_to_targets(params_id, |i| Some(self.source_location(params[i].span())));

        for (i, param) in params.iter().enumerate() {
            self.ast_info().params().insert(param.id(), ParamId(params_id, i));
        }

        params_id
    }

    /// Create a parameter list from the given AST parameter list, where the
    /// type of each parameter is a hole.
    pub(super) fn create_hole_params(&self, params: &ast::AstNodes<ast::Param>) -> ParamsId {
        self.create_hole_params_from(params, |param| &param.name)
    }
}
