use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    SequenceStoreKey, TrivialSequenceStoreKey,
};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::Context,
    tir::{validate_and_reorder_args_against_params, Arg, ArgsId, Node, NodeId, ParamsId},
};

use crate::{
    checker::Tc,
    env::TcEnv,
    errors::{TcError, TcResult},
    operations::{
        normalisation::{
            normalised_if, NormalisationOptions, NormalisationState, NormaliseResult,
            NormaliseSignal,
        },
        unification::UnificationOptions,
        RecursiveOperationsOnNode,
    },
};

impl<E: TcEnv> RecursiveOperationsOnNode<ArgsId> for Tc<'_, E> {
    type TyNode = ParamsId;
    type RecursiveArg = ArgsId;

    fn check_node_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        _: &mut Context,
        args: ArgsId,
        annotation_params: Self::TyNode,
        mut in_arg_scope: F,
    ) -> TcResult<T> {
        self.register_new_atom(args, annotation_params);
        let reordered_args_id = validate_and_reorder_args_against_params(args, annotation_params)?;

        let result = self.infer_some_args(
            reordered_args_id.iter(),
            annotation_params,
            |arg, param_ty| {
                let arg = arg.value();
                self.infer_term(arg.value, param_ty)?;
                Ok(())
            },
            |arg| {
                let arg = arg.value();
                Some(arg.value)
            },
            || in_arg_scope(reordered_args_id),
        )?;

        Ok(result)
    }

    fn normalise_node(
        &self,
        _ctx: &mut Context,
        opts: &NormalisationOptions,
        args_id: ArgsId,
    ) -> NormaliseResult<ArgsId> {
        let args = args_id.value();
        let st = NormalisationState::new();
        let ops = self.norm_ops_with(opts);

        let evaluated_arg_data = args
            .value()
            .into_iter()
            .map(|arg| -> Result<_, NormaliseSignal> {
                Ok(Node::at(
                    Arg {
                        target: arg.target,
                        value: (ops.eval_nested_and_record(arg.value.into(), &st)?).to_term(),
                    },
                    arg.origin,
                ))
            })
            .collect::<Result<Vec<_>, _>>()?;

        let new_node =
            Node::create_at(Node::<Arg>::seq(evaluated_arg_data), args_id.origin().computed());

        normalised_if(|| new_node, &st)
    }

    fn unify_nodes_rec<T, F: FnMut(Self::RecursiveArg) -> TcResult<T>>(
        &self,
        _ctx: &mut Context,
        opts: &UnificationOptions,
        src_id: ArgsId,
        target_id: ArgsId,
        mut f: F,
    ) -> TcResult<T> {
        if src_id.len() != target_id.len() {
            return Err(TcError::DifferentParamOrArgLengths {
                a: src_id.into(),
                b: target_id.into(),
            });
        }
        let uni_ops = self.uni_ops_with(opts);
        for (src_arg_id, target_arg_id) in src_id.iter().zip(target_id.iter()) {
            let src_arg = src_arg_id.value();
            let target_arg = target_arg_id.value();
            uni_ops.unify_terms(src_arg.value, target_arg.value)?;
        }
        f(src_id)
    }

    fn substitute_node_rec<T, F: FnMut(Self::RecursiveArg) -> T>(
        &self,
        _sub: &hash_tir::sub::Sub,
        _target: ArgsId,
        _f: F,
    ) -> T {
        todo!()
    }
}
