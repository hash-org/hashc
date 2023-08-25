//! Definitions related to modules.

use std::{fmt::Display, path::Path};

use hash_ast::ast;
use hash_source::{identifier::Identifier, SourceId};
use hash_storage::{
    static_sequence_store_direct, static_single_store,
    store::{statics::StoreId, SequenceStore, Store, StoreKey, TrivialSequenceStoreKey},
};
use textwrap::indent;
use utility_types::omit;

use super::{data::DataDefId, fns::FnDefId};
use crate::{
    ast_info::HasNodeId, environment::stores::tir_stores, symbols::Symbol,
    tir_debug_name_of_store_id, tir_get,
};

/// The kind of a module.
///
/// Might reference parameters in the mod def.
#[derive(Debug, Clone, Copy)]
pub enum ModKind {
    /// Defined as a module (`mod` block).
    ModBlock,
    /// Defined as a file module or interactive.
    ///
    /// Also contains the path to the file.
    Source(SourceId, &'static Path),
    /// Transparent
    ///
    /// Added by the compiler, used for primitives
    Transparent,
}

/// The right-hand side of a module member definition.
///
/// This can be:
/// - a function definition, e.g  x := () -> i32 => 42;
/// - a data definition, e.g.  x := struct(foo: str);
/// - a module definition, e.g.  x := mod {}
#[derive(Debug, Clone, Copy)]
pub enum ModMemberValue {
    /// A module member that is a definition.
    Data(DataDefId),
    /// A module member that is a nested module.
    Mod(ModDefId),
    /// A module member that is a function.
    Fn(FnDefId),
}

impl Display for ModMemberValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ModMemberValue::Data(data_def_id) => {
                write!(f, "{}", data_def_id)
            }
            ModMemberValue::Mod(mod_def_id) => {
                write!(f, "{}", mod_def_id)
            }
            ModMemberValue::Fn(fn_def_id) => {
                write!(f, "{}", fn_def_id)
            }
        }
    }
}

impl ModMemberValue {
    /// Get the name of the module member.
    pub fn name(&self) -> Symbol {
        match self {
            ModMemberValue::Data(data_def_id) => {
                tir_get!(*data_def_id, name)
            }
            ModMemberValue::Mod(mod_def_id) => {
                tir_get!(*mod_def_id, name)
            }
            ModMemberValue::Fn(fn_def_id) => {
                tir_get!(*fn_def_id, name)
            }
        }
    }
}

/// A member of a definition.
///
/// A definition might be a trait, impl block, or a module.
///
/// Includes a name, the original definition ID, an index into the original
/// definition's members, as well as the type of the member, and an optional
/// value of the member.
#[derive(Debug, Clone, Copy)]
#[omit(ModMemberData, [id], [Debug, Clone, Copy])]
pub struct ModMember {
    pub id: ModMemberId,
    pub name: Symbol,
    pub value: ModMemberValue,
}

static_sequence_store_direct!(
    store = pub ModMembersStore,
    id = pub ModMembersId[ModMemberId],
    value = ModMember,
    store_name = mod_members,
    store_source = tir_stores(),
    derives = Debug
);

/// A module definition.
///
/// This contains a name, parameters, a kind, and a set of members.
#[derive(Debug, Clone, Copy)]
#[omit(ModDefData, [id], [Debug, Clone, Copy])]
pub struct ModDef {
    /// The ID of the module definition.
    pub id: ModDefId,

    /// The name of the module.
    pub name: Symbol,
    /// The kind is parametrised over `params`.
    pub kind: ModKind,
    /// The members of the module.
    pub members: ModMembersId,
}

static_single_store!(
    store = pub ModDefStore,
    id = pub ModDefId,
    value = ModDef,
    store_name = mod_def,
    store_source = tir_stores()
);

impl HasNodeId for ModDefId {
    fn node_id(&self) -> Option<ast::AstNodeId> {
        tir_stores().ast_info().mod_defs().get_node_by_data(*self)
    }
}

tir_debug_name_of_store_id!(ModDefId);

impl ModDef {
    /// Get a module function member by name.
    pub fn get_mod_fn_member_by_ident(&self, name: impl Into<Identifier>) -> Option<FnDefId> {
        let name = name.into();
        self.members.iter().find_map(|member| {
            if let ModMemberValue::Fn(fn_def_id) = member.borrow().value {
                if member.borrow().name.borrow().name.is_some_and(|sym| sym == name) {
                    return Some(fn_def_id);
                }
            }
            None
        })
    }

    /// Get a module member by name.
    pub fn get_mod_member_by_ident(&self, name: impl Into<Identifier>) -> Option<ModMember> {
        let name = name.into();
        self.members.iter().find_map(|member| {
            if member.borrow().name.borrow().name.is_some_and(|sym| sym == name) {
                Some(member.value())
            } else {
                None
            }
        })
    }

    /// Iterate over all modules present in the sources.
    ///
    /// *Note*: this will not include modules created while iterating.
    pub fn iter_all_mods() -> impl Iterator<Item = ModDefId> {
        let member_count = tir_stores().mod_def().internal_data().read().len();
        (0..member_count).map(ModDefId::from_index_unchecked)
    }
}

impl Display for ModDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let members = (self.members).to_string();
        match self.kind {
            ModKind::ModBlock => {
                write!(f, "mod [name={}, type=block] {{\n{}}}", self.name, indent(&members, "  "))
            }
            ModKind::Source(_source_id, source_name) => {
                write!(
                    f,
                    "mod [name={}, type=file, src=\"{:?}\"] {{\n{}}}",
                    self.name,
                    source_name,
                    indent(&members, "  ")
                )
            }
            ModKind::Transparent => {
                write!(
                    f,
                    "mod [name={}, type=transparent] {{\n{}}}",
                    self.name,
                    indent(&members, "  ")
                )
            }
        }
    }
}

impl Display for ModDefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl Display for ModMember {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} := {}", self.name, self.value,)
    }
}

impl Display for ModMemberId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl Display for ModMembersId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for member in self.iter() {
            writeln!(f, "{}", member)?;
        }
        Ok(())
    }
}
