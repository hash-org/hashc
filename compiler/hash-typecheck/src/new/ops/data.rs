// @@Docs
use derive_more::Constructor;
use hash_types::new::{
    data::{CtorDef, CtorDefData, CtorDefsId, DataDef, DataDefId},
    defs::DefParamsId,
    environment::env::AccessToEnv,
    symbols::Symbol,
};
use hash_utils::store::{SequenceStore, Store};

use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

/// Data definition-related operations.
#[derive(Constructor)]
pub struct DataOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(DataOps<'tc>);

impl<'tc> DataOps<'tc> {
    /// Create an empty data definition.
    pub fn create_empty_data_def(&self, name: Symbol, params: DefParamsId) -> DataDefId {
        self.stores().data_def().create_with(|id| DataDef {
            id,
            name,
            params,
            ctors: self.stores().ctor_defs().create_from_slice(&[]),
        })
    }

    /// Set the constructors of the given data definition.
    pub fn set_data_def_ctors(&self, data_def: DataDefId, ctors: CtorDefsId) -> CtorDefsId {
        self.stores().data_def().modify_fast(data_def, |data_def| {
            data_def.ctors = ctors;
        });
        ctors
    }

    /// Create data constructors from the given iterator, for the given data
    /// definition.
    pub fn create_data_ctors<I: IntoIterator<Item = CtorDefData>>(
        &self,
        data_def_id: DataDefId,
        data: I,
    ) -> CtorDefsId
    where
        I::IntoIter: ExactSizeIterator,
    {
        self.stores().ctor_defs().create_from_iter_with(data.into_iter().enumerate().map(
            |(index, data)| {
                move |id| CtorDef {
                    id,
                    name: data.name,
                    data_def_id,
                    data_def_ctor_index: index,
                    params: data.params,
                    result_args: data.result_args,
                }
            },
        ))
    }
}
