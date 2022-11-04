use derive_more::Constructor;
use hash_types::new::{
    defs::{DefMember, DefMemberData, DefParamsId},
    mods::{ModDef, ModDefId, ModKind, ModMembersId},
    symbols::Symbol,
};
use hash_utils::store::{SequenceStore, Store};

use crate::{
    impl_access_to_tc_env,
    new::data::env::{AccessToTcEnv, TcEnv},
};

#[derive(Constructor)]
pub struct ModOps<'tc> {
    env: &'tc TcEnv<'tc>,
}

impl_access_to_tc_env!(ModOps<'tc>);

impl<'tc> ModOps<'tc> {
    pub fn create_mod_def(
        &self,
        name: Symbol,
        params: DefParamsId,
        kind: ModKind,
        self_ty_name: Option<Symbol>,
    ) -> ModDefId {
        self.stores().mod_def().create_with(|id| ModDef {
            id,
            name,
            params,
            kind,
            members: self.stores().mod_members().create_from_slice(&[]),
            self_ty_name,
        })
    }

    pub fn set_mod_def_members(&self, mod_def: ModDefId, members: ModMembersId) {
        self.stores().mod_def().modify_fast(mod_def, |mod_def| {
            mod_def.members = members;
        });
    }

    pub fn create_mod_members<I: IntoIterator<Item = DefMemberData>>(&self, data: I) -> ModMembersId
    where
        I::IntoIter: ExactSizeIterator,
    {
        self.stores().mod_members().create_from_iter_with(data.into_iter().map(|data| {
            move |id| DefMember { id, name: data.name, ty: data.ty, value: data.value }
        }))
    }
}
