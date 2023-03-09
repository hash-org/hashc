//! Utilities for parameters and arguments.
use derive_more::Constructor;
use hash_utils::{
    itertools::Itertools,
    store::{SequenceStore, SequenceStoreKey},
};

use super::common::CommonUtils;
use crate::{
    args::{Arg, ArgData, ArgsId, PatArg, PatArgData, PatArgsId, SomeArgsId},
    environment::env::{AccessToEnv, Env},
    impl_access_to_env,
    params::{Param, ParamData, ParamIndex, ParamsId},
    symbols::Symbol,
    terms::TermId,
};

#[derive(Constructor)]
pub struct ParamUtils<'env> {
    env: &'env Env<'env>,
}

impl_access_to_env!(ParamUtils<'env>);

impl<'env> ParamUtils<'env> {
    /// Create a new parameter list with the given names, and holes for all
    /// types.
    pub fn create_hole_params(
        &self,
        param_names: impl Iterator<Item = Symbol> + ExactSizeIterator,
    ) -> ParamsId {
        self.stores().params().create_from_iter_with(
            param_names
                .map(|name| move |id| Param { id, name, ty: self.new_ty_hole(), default: None }),
        )
    }

    /// Create a new parameter list with the given argument names, and holes for
    /// all types, and no default values.
    pub fn create_hole_params_from_args(&self, args: impl Into<SomeArgsId>) -> ParamsId {
        let args = args.into();
        self.create_hole_params(
            args.iter()
                .map(|arg| self.make_param_name_from_arg_index(self.get_arg_index(arg)))
                .collect_vec()
                .into_iter(),
        )
    }

    /// Create parameters from the given iterator of parameter data.
    pub fn create_params(
        &self,
        params: impl Iterator<Item = ParamData> + ExactSizeIterator,
    ) -> ParamsId {
        self.stores().params().create_from_iter_with(params.map(|data| {
            move |id| Param { id, name: data.name, ty: data.ty, default: data.default }
        }))
    }

    /// Create arguments from the given iterator of argument data.
    pub fn create_args(&self, args: impl Iterator<Item = ArgData> + ExactSizeIterator) -> ArgsId {
        self.stores().args().create_from_iter_with(
            args.map(|data| move |id| Arg { id, target: data.target, value: data.value }),
        )
    }

    /// Create pattern arguments from the given iterator of argument data.
    pub fn create_pat_args(
        &self,
        args: impl Iterator<Item = PatArgData> + ExactSizeIterator,
    ) -> PatArgsId {
        self.stores().pat_args().create_from_iter_with(
            args.map(|data| move |id| PatArg { id, target: data.target, pat: data.pat }),
        )
    }

    /// Create definition arguments for the given data definition
    ///
    /// Each argument will be a positional argument. Note that the outer
    /// iterator is for the argument groups, and the inner iterator is for
    /// the arguments in each group.
    pub fn create_positional_args(&self, args: impl IntoIterator<Item = TermId>) -> ArgsId {
        self.create_args(
            args.into_iter()
                .enumerate()
                .map(|(j, value)| ArgData { target: ParamIndex::Position(j), value })
                .collect_vec()
                .into_iter(),
        )
    }

    /// Instantiate the given parameters with holes for each argument.
    pub fn instantiate_params_as_holes(&self, params: ParamsId) -> ArgsId {
        self.create_args(
            params
                .iter()
                .enumerate()
                .map(|(i, _)| ArgData {
                    target: ParamIndex::Position(i),
                    value: self.new_term_hole(),
                })
                .collect_vec()
                .into_iter(),
        )
    }
}
