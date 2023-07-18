//! Utilities for parameters and arguments.
use derive_more::Constructor;
use hash_storage::store::{statics::StoreId, SequenceStore, TrivialSequenceStoreKey};
use hash_utils::itertools::Itertools;

use super::common::CommonUtils;
use crate::{
    args::{Arg, ArgData, ArgsId, PatArg, PatArgData, PatArgsId, SomeArgsId},
    environment::env::{AccessToEnv, Env},
    impl_access_to_env,
    params::{Param, ParamData, ParamIndex, ParamsId},
    symbols::Symbol,
    terms::{Term, TermId},
    tys::Ty,
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
            param_names.map(|name| move |_id| Param { name, ty: Ty::hole(), default: None }),
        )
    }

    /// Create a new parameter list with the given argument names, and holes for
    /// all types, and no default values.
    pub fn create_hole_params_from_args(&self, args: impl Into<SomeArgsId>) -> ParamsId {
        let args = args.into();
        self.create_hole_params(
            args.iter().map(|arg| self.get_arg_index(arg).into_symbol()).collect_vec().into_iter(),
        )
    }

    /// Create parameters from the given iterator of parameter data.
    pub fn create_params(
        &self,
        params: impl Iterator<Item = ParamData> + ExactSizeIterator,
    ) -> ParamsId {
        self.stores().params().create_from_iter_with(
            params.map(|data| {
                move |_id| Param { name: data.name, ty: data.ty, default: data.default }
            }),
        )
    }

    /// Create arguments from the given iterator of argument data.
    pub fn create_args(&self, args: impl Iterator<Item = ArgData> + ExactSizeIterator) -> ArgsId {
        self.stores().args().create_from_iter_with(
            args.map(|data| move |_id| Arg { target: data.target, value: data.value }),
        )
    }

    /// Create pattern arguments from the given iterator of argument data.
    pub fn create_pat_args(
        &self,
        args: impl Iterator<Item = PatArgData> + ExactSizeIterator,
    ) -> PatArgsId {
        self.stores().pat_args().create_from_iter_with(
            args.map(|data| move |_id| PatArg { target: data.target, pat: data.pat }),
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
        // @@Todo: locations
        self.create_args(
            params
                .iter()
                .enumerate()
                .map(|(i, _)| ArgData { target: ParamIndex::Position(i), value: Term::hole() })
                .collect_vec()
                .into_iter(),
        )
    }

    // Get the actual numerical parameter index from a given [ParamsId] and
    // [ParamIndex].
    pub fn try_get_actual_param_index(
        &self,
        params_id: ParamsId,
        index: ParamIndex,
    ) -> Option<usize> {
        match index {
            ParamIndex::Name(name) => self.stores().params().map_fast(params_id, |params| {
                params.iter().enumerate().find_map(|(i, param)| {
                    if param.name.value().name? == name {
                        Some(i)
                    } else {
                        None
                    }
                })
            }),
            ParamIndex::Position(pos) => Some(pos),
        }
    }
}
