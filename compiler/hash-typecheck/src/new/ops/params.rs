use derive_more::Constructor;
use hash_types::new::{
    args::{Arg, ArgData, ArgsId},
    defs::{
        DefArgGroup, DefArgGroupData, DefArgsId, DefParamGroup, DefParamGroupData, DefParamsId,
    },
    environment::env::AccessToEnv,
    params::{Param, ParamData, ParamsId},
    symbols::Symbol,
};
use hash_utils::store::SequenceStore;

use super::common::CommonOps;
use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

#[derive(Constructor)]
pub struct ParamOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(ParamOps<'tc>);

impl<'tc> ParamOps<'tc> {
    /// Create a new parameter list with the given names, and holes for all
    /// types.
    pub fn create_hole_params(
        &self,
        param_names: impl Iterator<Item = Symbol> + ExactSizeIterator,
    ) -> ParamsId {
        self.stores().params().create_from_iter_with(
            param_names.map(|name| {
                move |id| Param { id, name, ty: self.new_ty_hole(), default_value: None }
            }),
        )
    }

    /// Create definition parameters from the given iterator of parameter group
    /// data.
    pub fn create_def_params(
        &self,
        param_groups: impl Iterator<Item = DefParamGroupData> + ExactSizeIterator,
    ) -> DefParamsId {
        self.stores().def_params().create_from_iter_with(param_groups.map(|data| {
            move |id| DefParamGroup { id, params: data.params, implicit: data.implicit }
        }))
    }

    /// Create definition arguments from the given iterator of argument group
    /// data.
    pub fn create_def_args(
        &self,
        arg_groups: impl Iterator<Item = DefArgGroupData> + ExactSizeIterator,
    ) -> DefArgsId {
        self.stores().def_args().create_from_iter_with(arg_groups.map(|data| {
            move |id| DefArgGroup { id, args: data.args, param_group: data.param_group }
        }))
    }

    /// Create parameters from the given iterator of parameter data.
    pub fn create_params(
        &self,
        params: impl Iterator<Item = ParamData> + ExactSizeIterator,
    ) -> ParamsId {
        self.stores().params().create_from_iter_with(params.map(|data| {
            move |id| Param { id, name: data.name, ty: data.ty, default_value: data.default_value }
        }))
    }

    /// Create arguments from the given iterator of argument data.
    pub fn create_args(&self, args: impl Iterator<Item = ArgData> + ExactSizeIterator) -> ArgsId {
        self.stores().args().create_from_iter_with(
            args.map(|data| move |id| Arg { id, target: data.target, value: data.value }),
        )
    }
}
