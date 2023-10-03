use std::ops::ControlFlow;

use hash_storage::store::{statics::StoreId, SequenceStoreKey, TrivialSequenceStoreKey};
use hash_tir::{
    context::{HasContext, ScopeKind},
    tir::{validate_params, ParamsId, Term, Ty},
};

use crate::{
    env::TcEnv,
    errors::{TcError, TcResult},
    options::normalisation::{already_normalised, NormaliseResult},
    tc::Tc,
    traits::{OperationsOnNode, ScopedOperationsOnNode},
};

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

        let (result, shadowed_sub) =
            self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
                for param_id in params.iter() {
                    let param = param_id.value();
                    self.check_node(param.ty, Ty::universe_of(param.ty))?;
                    self.context().add_typing(param.name, param.ty);
                }

                let result = in_param_scope(())?;

                // Only keep the substitutions that do not refer to the parameters
                let scope_sub = self.substituter().create_sub_from_current_scope();
                let shadowed_sub = self.substituter().hide_param_binds(params.iter(), &scope_sub);
                Ok((result, shadowed_sub))
            })?;

        // Add the shadowed substitutions to the ambient scope
        self.add_sub_to_scope(&shadowed_sub);
        Ok(result)
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

        let (result, shadowed_sub) =
            self.context().enter_scope(ScopeKind::Sub, || -> TcResult<_> {
                for (src_param_id, target_param_id) in src_id.iter().zip(target_id.iter()) {
                    let src_param = src_param_id.value();
                    let target_param = target_param_id.value();

                    // Substitute the names
                    self.context().add_assignment(
                        src_param.name,
                        src_param.ty,
                        Term::from(target_param.name, target_param.origin),
                    );

                    // Unify the types
                    self.unify_nodes(src_param.ty, target_param.ty)?;
                    self.substituter().apply_sub_in_place(target_param.ty, &forward_sub);
                    self.substituter().apply_sub_in_place(src_param.ty, &backward_sub);
                }

                // Run the in-scope closure
                let result = in_param_scope(())?;

                // Only keep the substitutions that do not refer to the parameters
                let scope_sub = self.substituter().create_sub_from_current_scope();
                let shadowed_sub = self
                    .substituter()
                    .hide_param_binds(src_id.iter().chain(target_id.iter()), &scope_sub);
                Ok((result, shadowed_sub))
            })?;

        // Add the shadowed substitutions to the ambient scope
        self.add_sub_to_scope(&shadowed_sub);

        Ok(result)
    }
}
