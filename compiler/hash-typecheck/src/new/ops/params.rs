use derive_more::Constructor;
use hash_types::new::{
    defs::{DefParamGroup, DefParamGroupData, DefParamsId},
    environment::env::AccessToEnv,
    params::{Param, ParamsId},
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
}
