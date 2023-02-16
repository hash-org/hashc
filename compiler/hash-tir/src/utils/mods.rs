//! Module-related utilities.
use derive_more::Constructor;
use hash_source::identifier::Identifier;
use hash_utils::store::{CloneStore, SequenceStore, SequenceStoreKey, Store, StoreKey};
use itertools::Itertools;

use super::common::CommonUtils;
use crate::{
    environment::env::{AccessToEnv, Env},
    fns::FnDefId,
    impl_access_to_env,
    mods::{ModDef, ModDefData, ModDefId, ModMember, ModMemberData, ModMemberValue, ModMembersId},
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
    pub fn create_mod_members<I: IntoIterator<Item = ModMemberData>>(
        &self,
        data: I,
    ) -> ModMembersId {
        self.stores().mod_members().create_from_iter_with(
            data.into_iter()
                .map(|data| move |id| ModMember { id, name: data.name, value: data.value })
                .collect_vec(),
        )
    }

    /// Get a module function member by name.
    pub fn get_mod_fn_member_by_ident(
        &self,
        mod_def_id: ModDefId,
        name: impl Into<Identifier>,
    ) -> Option<FnDefId> {
        let name = name.into();
        self.stores().mod_def().map_fast(mod_def_id, |def| {
            self.stores().mod_members().map_fast(def.members, |members| {
                members.iter().find_map(|&member| {
                    if let ModMemberValue::Fn(fn_def_id) = member.value {
                        if self.get_symbol(member.name).name.contains(&name) {
                            return Some(fn_def_id);
                        }
                    }
                    None
                })
            })
        })
    }

    /// Get a module member by name.
    pub fn get_mod_member_by_ident(
        &self,
        mod_def_id: ModDefId,
        name: impl Into<Identifier>,
    ) -> Option<ModMember> {
        let name = name.into();
        self.stores().mod_def().map_fast(mod_def_id, |def| {
            self.stores().mod_members().map_fast(def.members, |members| {
                members
                    .iter()
                    .find(|&member| self.get_symbol(member.name).name.contains(&name))
                    .copied()
            })
        })
    }

    /// Iterate over all modules present in the sources.
    ///
    /// *Note*: this will not include modules created while iterating.
    pub fn iter_all_mods(&self) -> impl Iterator<Item = ModDefId> + '_ {
        let member_count = self.stores().mod_def().internal_data().borrow().len();
        (0..member_count).map(ModDefId::from_index_unchecked)
    }

    /// Iterate over the members of the given module definition.
    ///
    /// *Note*: this will not include members created while iterating.
    pub fn iter_mod_members(&self, mod_def_id: ModDefId) -> impl Iterator<Item = ModMember> + '_ {
        let mod_def = self.stores().mod_def().get(mod_def_id);
        mod_def.members.iter().map(|member_id| self.stores().mod_members().get_element(member_id))
    }
}