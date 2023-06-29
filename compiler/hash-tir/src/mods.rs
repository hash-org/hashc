//! Definitions related to modules.

use std::fmt::Display;

use hash_source::SourceId;
use hash_utils::store::{SequenceStore, Store, TrivialSequenceStoreKey};
use textwrap::indent;
use utility_types::omit;

use super::{data::DataDefId, fns::FnDefId};
use crate::{
    environment::stores::StoreId, symbols::Symbol, tir_debug_name_of_store_id, tir_get,
    tir_sequence_store_direct, tir_single_store,
};

/// The kind of a module.
///
/// Might reference parameters in the mod def.
#[derive(Debug, Clone, Copy)]
pub enum ModKind {
    /// Defined as a module (`mod` block).
    ModBlock,
    /// Defined as a file module or interactive.
    Source(SourceId),
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
                write!(f, "{}", (data_def_id))
            }
            ModMemberValue::Mod(mod_def_id) => {
                write!(f, "{}", (mod_def_id))
            }
            ModMemberValue::Fn(fn_def_id) => {
                write!(f, "{}", (fn_def_id))
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

tir_sequence_store_direct!(
    store = pub ModMembersStore,
    id = pub ModMembersId[ModMemberId],
    value = ModMember,
    store_name = mod_members,
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

tir_single_store!(
    store = pub ModDefStore,
    id = pub ModDefId,
    value = ModDef,
    store_name = mod_def
);

tir_debug_name_of_store_id!(ModDefId);

impl Display for ModDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let members = (self.members).to_string();
        match self.kind {
            ModKind::ModBlock => {
                write!(f, "mod [name={}, type=block] {{\n{}}}", (self.name), indent(&members, "  "))
            }
            ModKind::Source(source_id) => {
                // @@Todo: source name
                // let source_name = self.env().source_map().source_name(source_id);
                write!(
                    f,
                    "mod [name={}, type=file, src=\"{:?}\"] {{\n{}}}",
                    (self.name),
                    source_id,
                    indent(&members, "  ")
                )
            }
            ModKind::Transparent => {
                write!(
                    f,
                    "mod [name={}, type=transparent] {{\n{}}}",
                    (self.name),
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
        write!(f, "{} := {}", (self.name), (self.value),)
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
            writeln!(f, "{}", (member))?;
        }
        Ok(())
    }
}
