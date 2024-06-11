use std::ops::ControlFlow;

use hash_storage::store::{
    statics::{SequenceStoreValue, SingleStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_tir::{
    context::{HasContext, ScopeKind},
    tir::{
        validate_params, Arg, ArgsId, Node, NodeId, NodeOrigin, Param, ParamIndex, ParamsId,
        SymbolId, Term, Ty,
    },
};
use itertools::Itertools;

use crate::{
    diagnostics::{TcError, TcResult},
    env::TcEnv,
    options::normalisation::{already_normalised, NormaliseResult},
    tc::Tc,
    traits::{OperationsOnNode, ScopedOperationsOnNode},
};

impl<E: TcEnv> Tc<'_, E> {
    /// Create a new parameter list with the given names, and holes for all
    /// types (the second slot of the iterator value is the origin of the
    /// inferred type).
    pub fn params_from_names_with_hole_types(
        &self,
        param_names: impl Iterator<Item = (SymbolId, NodeOrigin)>,
        origin: NodeOrigin,
    ) -> ParamsId {
        Node::create(Node::at(
            Node::seq(
                param_names
                    .map(|(name, ty_origin)| {
                        Node::at(
                            Param { name, ty: self.fresh_meta(ty_origin), default: None },
                            ty_origin,
                        )
                    })
                    .collect_vec(),
            ),
            origin,
        ))
    }

    /// Create a new parameter list with the given argument names, and holes for
    /// all types, and no default values.
    pub fn params_from_args_with_hole_types(&self, args: ArgsId) -> ParamsId {
        self.params_from_names_with_hole_types(
            args.iter().map(|arg| {
                (
                    match arg.value().data.target {
                        ParamIndex::Name(name) => SymbolId::from_name(name, arg.origin()),
                        ParamIndex::Position(_) => SymbolId::fresh(arg.origin()),
                    },
                    arg.origin().inferred(),
                )
            }),
            args.origin().inferred(),
        )
    }

    /// Instantiate the given parameters with holes for each argument.
    ///
    /// This will use the origin of the parameters wrapped in
    /// [`NodeOrigin::InferredFrom`].
    pub fn args_from_params_as_holes(&self, params_id: ParamsId) -> ArgsId {
        Node::create_at(
            Node::seq(
                params_id
                    .value()
                    .iter()
                    .enumerate()
                    .map(|(i, param)| {
                        Node::at(
                            Arg {
                                target: ParamIndex::pos(i),
                                value: Term::fresh_hole(param.origin().computed()),
                            },
                            param.origin().computed(),
                        )
                    })
                    .collect_vec(),
            ),
            params_id.origin().computed(),
        )
    }

    /// Instantiate the given parameters with holes for each argument.
    ///
    /// This will use the origin of the parameters wrapped in
    /// [`NodeOrigin::InferredFrom`].
    pub fn args_from_params_as_metas(&self, params_id: ParamsId) -> ArgsId {
        Node::create_at(
            Node::seq(
                params_id
                    .value()
                    .iter()
                    .enumerate()
                    .map(|(i, param)| {
                        Node::at(
                            Arg {
                                target: ParamIndex::pos(i),
                                value: self.fresh_meta(param.origin().computed()),
                            },
                            param.origin().computed(),
                        )
                    })
                    .collect_vec(),
            ),
            params_id.origin().computed(),
        )
    }

    // Enter a parameter scope
    pub(crate) fn enter_params_scope<T, F: FnOnce() -> TcResult<T>>(
        &self,
        params: ParamsId,
        in_param_scope: F,
    ) -> TcResult<T> {
        // Enter the scope
        self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
            for param_id in params.iter() {
                let param = param_id.value();
                self.context().add_typing(param.name, param.ty);
            }

            in_param_scope()
        })
    }
}

impl<E: TcEnv> ScopedOperationsOnNode<ParamsId> for Tc<'_, E> {
    type AnnotNode = ();
    type CallbackArg = ();

    fn check_node_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        params: ParamsId,
        _: Self::AnnotNode,
        mut in_param_scope: F,
    ) -> TcResult<T> {
        // Validate the parameters
        validate_params(params)?;

        self.context().enter_scope(ScopeKind::Sub, || {
            for param_id in params.iter() {
                let param = param_id.value();
                self.check_node(param.ty, Ty::universe_of(param.ty))?;
                self.context().add_typing(param.name, param.ty);
            }

            let result = in_param_scope(())?;

            Ok(result)
        })
    }

    fn try_normalise_node(&self, _item: ParamsId) -> NormaliseResult<ControlFlow<ParamsId>> {
        already_normalised()
    }

    fn unify_nodes_scoped<T, F: FnMut(Self::CallbackArg) -> TcResult<T>>(
        &self,
        src_id: ParamsId,
        target_id: ParamsId,
        mut in_param_scope: F,
    ) -> TcResult<T> {
        // Validate the parameters and ensure they are of the same length
        validate_params(src_id)?;
        validate_params(target_id)?;
        if src_id.len() != target_id.len() {
            return Err(TcError::WrongParamLength {
                given_params_id: src_id,
                annotation_params_id: target_id,
            });
        }

        let forward_sub = self.substituter().create_sub_from_param_names(src_id, target_id);
        let backward_sub = self.substituter().create_sub_from_param_names(target_id, src_id);

        for (src_param_id, target_param_id) in src_id.iter().zip(target_id.iter()) {
            let src_param = src_param_id.value();
            let target_param = target_param_id.value();

            // Substitute the names
            // self.context().add_typed_assignment(
            //     src_param.name,
            //     src_param.ty,
            //     Term::from(target_param.name, target_param.origin),
            // );

            // Unify the types
            self.unify_nodes(src_param.ty, target_param.ty)?;
            self.substituter().apply_sub_in_place(target_param.ty, &forward_sub);
            self.substituter().apply_sub_in_place(src_param.ty, &backward_sub);
        }

        // Run the in-scope closure
        let result = in_param_scope(())?;

        // Only keep the substitutions that do not refer to the parameters
        Ok(result)
    }
}
