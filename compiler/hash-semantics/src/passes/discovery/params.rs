//! Utilities for creating parameters and arguments during discovery.
use hash_ast::ast::{self, AstNodeId};
use hash_storage::store::statics::{SequenceStoreValue, SingleStoreValue};
use hash_tir::tir::{Node, NodeOrigin, NodesId, Param, ParamId, ParamIndex, ParamsId, Term};

use super::DiscoveryPass;
use crate::env::SemanticEnv;

impl<'env, E: SemanticEnv> DiscoveryPass<'env, E> {
    /// Create a parameter list from the given AST generic parameter list, where
    /// the type of each parameter is a unresolved.
    pub(super) fn create_unresolved_params_from<T>(
        &self,
        params: &ast::AstNodes<T>,
        name: impl Fn(&T) -> &Option<ast::AstNode<ast::Name>>,
    ) -> ParamsId {
        let params_id = Node::create_at(
            Node::seq(params.iter().enumerate().map(|(i, param)| {
                Node::at(
                    match name(param) {
                        Some(name) => Param {
                            name: ParamIndex::Name(name.ident)
                                .into_symbol(NodeOrigin::Given(name.id())),
                            ty: Term::unresolved(NodeOrigin::Given(name.id())),
                            default: None,
                        },
                        None => Param {
                            name: ParamIndex::Position(i as u32)
                                .into_symbol(NodeOrigin::Given(param.id())),
                            ty: Term::unresolved(NodeOrigin::Given(param.id())),
                            default: None,
                        },
                    },
                    NodeOrigin::Given(param.id()),
                )
            })),
            NodeOrigin::Given(params.id()),
        );

        for (i, param) in params.iter().enumerate() {
            self.ast_info.params().insert(param.id(), ParamId::new(params_id.elements(), i));
        }

        params_id
    }

    /// Create a parameter list from the given AST parameter list, where the
    /// type of each parameter is a unresolved.
    pub(super) fn create_unresolved_params_from_params(
        &self,
        node: Option<&ast::AstNode<ast::Params>>,
        alternative_origin: AstNodeId,
    ) -> ParamsId {
        if let Some(params) = node {
            self.create_unresolved_params_from(&params.params, |param| &param.name)
        } else {
            Node::create_at(Node::<Param>::empty_seq(), NodeOrigin::Given(alternative_origin))
        }
    }

    /// Create a parameter list from the given AST parameter list, where the
    /// type of each parameter is a unresolved.
    pub(super) fn create_unresolved_params_from_ty_params(
        &self,
        params: Option<&ast::AstNode<ast::TyParams>>,
        alternative_origin: AstNodeId,
    ) -> ParamsId {
        if let Some(ty_params) = params {
            self.create_unresolved_params_from(&ty_params.params, |param| &param.name)
        } else {
            Node::create_at(Node::<Param>::empty_seq(), NodeOrigin::Given(alternative_origin))
        }
    }
}
