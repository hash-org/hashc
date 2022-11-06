use derive_more::Constructor;
use hash_types::new::{
    data::{CtorDef, CtorDefsId, DataDef, DataDefId},
    defs::{DefMemberData, DefParamsId},
    environment::env::AccessToEnv,
    symbols::Symbol,
};
use hash_utils::store::{SequenceStore, Store};

use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

#[derive(Constructor)]
pub struct DataOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(DataOps<'tc>);

impl<'tc> DataOps<'tc> {
    pub fn create_empty_data_def(&self, name: Symbol, params: DefParamsId) -> DataDefId {
        self.stores().data_def().create_with(|id| DataDef {
            id,
            name,
            params,
            ctors: self.stores().ctor_defs().create_from_slice(&[]),
        })
    }

    pub fn set_data_def_ctors(&self, data_def: DataDefId, ctors: CtorDefsId) {
        self.stores().data_def().modify_fast(data_def, |data_def| {
            data_def.ctors = ctors;
        });
    }

    pub fn create_data_ctors_from_members<I: IntoIterator<Item = DefMemberData>>(
        &self,
        data_def_id: DataDefId,
        data: I,
    ) -> CtorDefsId
    where
        I::IntoIter: ExactSizeIterator,
    {
        self.stores().ctor_defs().create_from_iter_with(data.into_iter().enumerate().map(
            |(index, data)| {
                // @@Todo: deal with parameters
                move |id| CtorDef {
                    id,
                    name: data.name,
                    data_def_id,
                    data_def_ctor_index: index,
                    params: self.stores().def_params().create_empty(),
                    result_args: self.stores().def_args().create_empty(),
                }
            },
        ))
    }
}
