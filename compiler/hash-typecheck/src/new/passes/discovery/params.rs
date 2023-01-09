//! Utilities for creating parameters and arguments during discovery.
use hash_ast::ast::{self};
use hash_types::new::{
    defs::{DefParamGroupData, DefParamsId},
    environment::env::AccessToEnv,
    params::{ParamData, ParamsId},
};
use itertools::Itertools;

use super::DiscoveryPass;
use crate::new::{
    ops::{common::CommonOps, AccessToOps},
    passes::ast_utils::AstUtils,
};

impl<'tc> DiscoveryPass<'tc> {
    /// Create definition params from the iterator of parameter groups.
    ///
    /// The iterator elements are `(is_implicit, params)`.
    pub(super) fn create_hole_def_params<'a>(
        &self,
        groups: impl Iterator<Item = (bool, &'a ast::AstNodes<ast::Param>)>,
    ) -> DefParamsId {
        let groups = groups.collect_vec();
        let params = groups
            .iter()
            .copied()
            .map(|group| {
                let (implicit, params) = group;
                DefParamGroupData { params: self.create_hole_params(params), implicit }
            })
            .collect_vec();

        let def_params = self.param_ops().create_def_params(params.into_iter());
        self.stores().location().add_locations_to_targets(def_params, |i| {
            Some(self.source_location(groups[i].1.span()?))
        });
        def_params
    }

    /// Create a parameter list from the given AST parameter list, where the
    /// type of each parameter is a hole.
    pub(super) fn create_hole_params(&self, params: &ast::AstNodes<ast::Param>) -> ParamsId {
        self.param_ops().create_hole_params(
            params.iter().map(|param| self.create_symbol_from_ast_name(&param.name)),
        )
    }

    /// Create a parameter data list from the given AST parameter list, where
    /// the type and default value of each parameter is a hole.
    pub(super) fn create_param_data_from_ast_params<'a>(
        &self,
        params: impl Iterator<Item = &'a ast::AstNode<ast::Param>> + ExactSizeIterator,
    ) -> Vec<ParamData> {
        params
            .map(|param| {
                let name = self.create_symbol_from_ast_name(&param.name);
                let ty = self.new_ty_hole();
                let default_value = param.default.as_ref().map(|_| self.new_term_hole());
                ParamData { name, ty, default_value }
            })
            .collect_vec()
    }
}
