// @@Docs
use derive_more::Constructor;
use hash_utils::store::{SequenceStore, Store};

use crate::{
    impl_access_to_env,
    new::{
        environment::env::{AccessToEnv, Env},
        mods::{ModDef, ModDefData, ModDefId, ModMember, ModMemberData, ModMembersId},
    },
};

/// Operations related to module definitions.
#[derive(Constructor)]
pub struct ModUtils<'tc> {
    env: &'tc Env<'tc>,
}

impl_access_to_env!(ModUtils<'tc>);

impl<'tc> ModUtils<'tc> {
    /// Create an empty module definition.
    pub fn create_mod_def(&self, data: ModDefData) -> ModDefId {
        self.stores().mod_def().create_with(|id| ModDef {
            id,
            name: data.name,
            kind: data.kind,
            members: data.members,
        })
    }

    /// Set the members of the given module definition.
    pub fn set_mod_def_members(&self, mod_def: ModDefId, members: ModMembersId) -> ModMembersId {
        self.stores().mod_def().modify_fast(mod_def, |mod_def| {
            mod_def.members = members;
        });
        members
    }

    /// Create an empty set of module members.
    pub fn create_empty_mod_members(&self) -> ModMembersId {
        self.stores().mod_members().create_from_slice(&[])
    }

    /// Create module members from the given set of members as an iterator.
    pub fn create_mod_members<I: IntoIterator<Item = ModMemberData>>(&self, data: I) -> ModMembersId
    where
        I::IntoIter: ExactSizeIterator,
    {
        self.stores().mod_members().create_from_iter_with(
            data.into_iter()
                .map(|data| move |id| ModMember { id, name: data.name, value: data.value }),
        )
    }
}
