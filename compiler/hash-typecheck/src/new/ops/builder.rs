use derive_more::Constructor;
use hash_source::identifier::Identifier;
use hash_types::new::{
    defs::{DefParamGroup, DefParamGroupData, DefParamsId},
    params::{Param, ParamData, ParamsId},
    symbols::{Symbol, SymbolData},
};
use hash_utils::store::{SequenceStore, Store};

use crate::{
    impl_access_to_tc_env,
    new::data::env::{AccessToTcEnv, TcEnv},
};

#[derive(Constructor)]
pub struct Builder<'env> {
    env: &'env TcEnv<'env>,
}

impl_access_to_tc_env!(Builder<'env>);

impl<'env> Builder<'env> {
    pub fn create_internal_symbol(&self) -> Symbol {
        self.stores().symbol().create_with(|symbol| SymbolData { name: None, symbol })
    }

    pub fn create_symbol(&self, name: impl Into<Identifier>) -> Symbol {
        self.stores().symbol().create_with(|symbol| SymbolData { name: Some(name.into()), symbol })
    }

    pub fn create_params<I: IntoIterator<Item = ParamData>>(&self, data: I) -> ParamsId
    where
        I::IntoIter: ExactSizeIterator,
    {
        self.stores().params().create_from_iter_with(data.into_iter().map(|data| {
            move |id| Param { id, default_value: data.default_value, name: data.name, ty: data.ty }
        }))
    }

    pub fn create_def_params<I: IntoIterator<Item = DefParamGroupData>>(
        &self,
        data: I,
    ) -> DefParamsId
    where
        I::IntoIter: ExactSizeIterator,
    {
        self.stores().def_params().create_from_iter_with(data.into_iter().map(|data| {
            move |id| DefParamGroup { id, params: data.params, implicit: data.implicit }
        }))
    }
}
