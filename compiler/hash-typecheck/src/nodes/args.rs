use hash_storage::store::{statics::StoreId, TrivialSequenceStoreKey};
use hash_tir::{
    atom_info::ItemInAtomInfo,
    context::Context,
    tir::{validate_and_reorder_args_against_params, ArgsId, ParamsId},
};

use crate::{
    checker::Checker,
    env::TcEnv,
    operations::{
        checking::{did_check, CheckResult, CheckState},
        normalisation::NormaliseResult,
        unification::UnifyResult,
        RecursiveOperations,
    },
};

impl<E: TcEnv> RecursiveOperations<ArgsId> for Checker<'_, E> {
    type TyNode = ParamsId;
    type Node = ArgsId;
    type RecursiveArg = ArgsId;

    fn check_rec<T, F: FnMut(Self::RecursiveArg) -> CheckResult<T>>(
        &self,
        _: &mut Context,
        args: &mut ArgsId,
        annotation_params: Self::TyNode,
        _: Self::Node,
        mut in_arg_scope: F,
    ) -> CheckResult<T> {
        let args = *args;
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
            || CheckState::new().then_result(in_arg_scope(reordered_args_id)),
        )?;

        did_check(result)
    }

    fn normalise_rec<T, F: FnMut(Self::RecursiveArg) -> NormaliseResult<T>>(
        &self,
        _ctx: &mut Context,
        _item: &mut ArgsId,
        _item_node: Self::Node,
        _f: F,
    ) -> NormaliseResult<T> {
        todo!()
    }

    fn unify_rec<T, F: FnMut(Self::RecursiveArg) -> UnifyResult<T>>(
        &self,
        _ctx: &mut Context,
        _src: &mut ArgsId,
        _target: &mut ArgsId,
        _src_node: Self::Node,
        _target_node: Self::Node,
        _f: F,
    ) -> UnifyResult<T> {
        todo!()
    }

    fn substitute_rec<T, F: FnMut(Self::RecursiveArg) -> T>(
        &self,
        _sub: &hash_tir::sub::Sub,
        _target: &mut ArgsId,
        _f: F,
    ) -> T {
        todo!()
    }
}