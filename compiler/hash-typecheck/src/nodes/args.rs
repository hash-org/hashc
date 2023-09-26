use hash_storage::store::{
    statics::{SequenceStoreValue, StoreId},
    TrivialSequenceStoreKey,
};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::Context,
    tir::{validate_and_reorder_args_against_params, Arg, ArgsId, Node, NodeId, ParamsId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    errors::TcResult,
    operations::{
        normalisation::{
            normalised_if, NormalisationOptions, NormalisationState, NormaliseResult,
            NormaliseSignal,
        },
        unification::UnificationOptions,
        RecursiveOperationsOnNode,
    },
};

impl<E: TcEnv> RecursiveOperationsOnNode<ArgsId> for Checker<'_, E> {
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

        let result = self.infer_ops().infer_some_args(
            reordered_args_id.iter(),
            annotation_params,
            |arg, param_ty| {
                let arg = arg.value();
                self.infer_ops().infer_term(arg.value, param_ty)?;
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
        _opts: &UnificationOptions,
        _src: ArgsId,
        _target: ArgsId,
        _f: F,
    ) -> TcResult<T> {
        todo!()
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
