// @@Docs
use derive_more::Constructor;
use hash_types::new::{
    defs::{DefMember, DefMemberData, DefParamsId},
    environment::env::AccessToEnv,
    symbols::Symbol,
    trts::{TrtDef, TrtDefId, TrtMembersId},
};
use hash_utils::store::{SequenceStore, Store};

use crate::{impl_access_to_tc_env, new::environment::tc_env::TcEnv};

/// Operations related to trait definitions.
#[derive(Constructor)]
pub struct TrtOps<'tc> {
    tc_env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(TrtOps<'tc>);

impl<'tc> TrtOps<'tc> {
    /// Create an empty trait definition.
    pub fn create_trt_def(
        &self,
        name: Symbol,
        params: DefParamsId,
        self_ty_name: Symbol,
    ) -> TrtDefId {
        self.stores().trt_def().create_with(|id| TrtDef {
            id,
            name,
            params,
            members: self.stores().trt_members().create_from_slice(&[]),
            self_ty_name,
        })
    }

    /// Set the members of the given trait definition.
    pub fn set_trt_def_members(&self, trt_def: TrtDefId, members: TrtMembersId) {
        self.stores().trt_def().modify_fast(trt_def, |trt_def| {
            trt_def.members = members;
        });
    }

    /// Create trait members from the given set of members as an iterator.
    pub fn create_trt_members<I: IntoIterator<Item = DefMemberData>>(&self, data: I) -> TrtMembersId
    where
        I::IntoIter: ExactSizeIterator,
    {
        self.stores().trt_members().create_from_iter_with(data.into_iter().map(|data| {
            move |id| DefMember { id, name: data.name, ty: data.ty, value: data.value }
        }))
    }
}
