use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    context::ScopeKind,
    tir::{validate_params, ParamsId, Ty},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::TcResult,
    operations::{
        normalisation::{NormalisationOptions, NormaliseResult},
        unification::UnificationOptions,
        OperationsOnNode, RecursiveOperationsOnNode,
    },
};

impl<E: TcEnv> RecursiveOperationsOnNode<ParamsId> for Tc<'_, E> {
    type TyNode = ();
    type RecursiveArg = ();

    fn check_node_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        params: ParamsId,
        _: Self::TyNode,
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
                let scope_sub = self.sub_ops().create_sub_from_current_scope();
                let shadowed_sub = self.sub_ops().hide_param_binds(params.iter(), &scope_sub);
                Ok((result, shadowed_sub))
            })?;

        // Add the shadowed substitutions to the ambient scope
        self.uni_ops().add_unification_from_sub(&shadowed_sub);
        Ok(result)
    }

    fn normalise_node(
        &self,
        _opts: &NormalisationOptions,
        _item: ParamsId,
    ) -> NormaliseResult<ParamsId> {
        todo!()
    }

    fn unify_nodes_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        _opts: &UnificationOptions,
        _src: ParamsId,
        _target: ParamsId,
        _f: F,
    ) -> TcResult<T> {
        todo!()
    }

    fn substitute_node_rec<T, F: FnMut(Self::RecursiveArg) -> T>(
        &self,
        _sub: &hash_tir::sub::Sub,
        _target: ParamsId,
        _f: F,
    ) -> T {
        todo!()
    }
}
