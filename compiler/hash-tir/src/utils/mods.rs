//! Module-related utilities.
use derive_more::Constructor;
use hash_ast::ast::OwnsAstNode;
use hash_source::{identifier::Identifier, ModuleId};
use hash_utils::{
    itertools::Itertools,
    store::{CloneStore, SequenceStore, SequenceStoreKey, Store, StoreKey},
};

use super::common::CommonUtils;
use crate::{
    environment::env::{AccessToEnv, Env},
    fns::FnDefId,
    impl_access_to_env,
    mods::{
        ModDef, ModDefData, ModDefId, ModKind, ModMember, ModMemberData, ModMemberValue,
        ModMembersId,
    },
};

/// Operations related to module definitions.
#[derive(Constructor)]
pub struct ModUtils<'tc> {
    env: &'tc Env<'tc>,
}

impl_access_to_env!(ModUtils<'tc>);

impl<'tc> ModUtils<'tc> {
    /// Create or get an existing module definition by `[SourceId]`.
    pub fn create_or_get_module_mod_def(&self, module_id: ModuleId) -> ModDefId {
        let source_node_id = self.node_map().get_module(module_id).node_ref().id();
        match self.stores().ast_info().mod_defs().get_data_by_node(source_node_id) {
            Some(existing) => existing,
            None => {
                // Create a new module definition.
                let source_id = module_id.into();
                let module_name: Identifier = self.source_map().source_name(source_id).into();
                let mod_def_id = self.create_mod_def(ModDefData {
                    name: self.new_symbol(module_name),
                    kind: ModKind::Source(source_id),
                    members: self.create_empty_mod_members(),
                });
                self.stores().ast_info().mod_defs().insert(source_node_id, mod_def_id);
                mod_def_id
            }
        }
    }

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
                        if self.get_symbol(member.name).name.is_some_and(|sym| sym == name) {
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
                    .find(|&member| {
                        self.get_symbol(member.name).name.is_some_and(|sym| sym == name)
                    })
                    .copied()
            })
        })
    }

    /// Iterate over all modules present in the sources.
    ///
    /// *Note*: this will not include modules created while iterating.
    pub fn iter_all_mods(&self) -> impl Iterator<Item = ModDefId> + '_ {
        let member_count = self.stores().mod_def().internal_data().read().len();
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
