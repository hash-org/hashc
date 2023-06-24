//! Definitions related to modules.

use std::fmt::Display;

use hash_source::SourceId;
use hash_utils::{
    new_sequence_store_key, new_store, new_store_key,
    store::{CloneStore, DefaultSequenceStore, SequenceStore, Store},
};
use textwrap::indent;
use utility_types::omit;

use super::{
    data::DataDefId,
    environment::env::{AccessToEnv, WithEnv},
    fns::FnDefId,
};
use crate::{impl_sequence_store_id, impl_single_store_id, symbols::Symbol};

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

impl Display for WithEnv<'_, ModMemberValue> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            ModMemberValue::Data(data_def_id) => {
                write!(f, "{}", self.env().with(data_def_id))
            }
            ModMemberValue::Mod(mod_def_id) => {
                write!(f, "{}", self.env().with(mod_def_id))
            }
            ModMemberValue::Fn(fn_def_id) => {
                write!(f, "{}", self.env().with(fn_def_id))
            }
        }
    }
}

impl WithEnv<'_, ModMemberValue> {
    /// Get the name of the module member.
    pub fn name(&self) -> Symbol {
        match self.value {
            ModMemberValue::Data(data_def_id) => {
                self.env().stores().data_def().map_fast(data_def_id, |def| def.name)
            }
            ModMemberValue::Mod(mod_def_id) => {
                self.env().stores().mod_def().map_fast(mod_def_id, |def| def.name)
            }
            ModMemberValue::Fn(fn_def_id) => {
                self.env().stores().fn_def().map_fast(fn_def_id, |def| def.name)
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

new_sequence_store_key!(pub ModMembersId);
pub type ModMembersStore = DefaultSequenceStore<ModMembersId, ModMember>;
pub type ModMemberId = (ModMembersId, usize);
impl_sequence_store_id!(ModMembersId, ModMember, mod_members);

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

new_store_key!(pub ModDefId);
new_store!(pub ModDefStore<ModDefId, ModDef>);
impl_single_store_id!(ModDefId, ModDef, mod_def);

impl Display for WithEnv<'_, &ModDef> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let members = self.env().with(self.value.members).to_string();
        match self.value.kind {
            ModKind::ModBlock => {
                write!(
                    f,
                    "mod [name={}, type=block] {{\n{}}}",
                    self.env().with(self.value.name),
                    indent(&members, "  ")
                )
            }
            ModKind::Source(source_id) => {
                let source_name = self.env().source_map().source_name(source_id);
                write!(
                    f,
                    "mod [name={}, type=file, src=\"{source_name}\"] {{\n{}}}",
                    self.env().with(self.value.name),
                    indent(&members, "  ")
                )
            }
            ModKind::Transparent => {
                write!(
                    f,
                    "mod [name={}, type=transparent] {{\n{}}}",
                    self.env().with(self.value.name),
                    indent(&members, "  ")
                )
            }
        }
    }
}

impl Display for WithEnv<'_, ModDefId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.stores().mod_def().map_fast(self.value, |def| write!(f, "{}", self.env().with(def)))
    }
}

impl Display for WithEnv<'_, &ModMember> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} := {}", self.env().with(self.value.name), self.env().with(self.value.value),)
    }
}

impl Display for WithEnv<'_, ModMemberId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.stores().mod_members().map_fast(self.value.0, |members| {
            writeln!(f, "{}", self.env().with(&members[self.value.1]))
        })
    }
}

impl Display for WithEnv<'_, ModMembersId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.stores().mod_members().map_fast(self.value, |members| {
            for member in members.iter() {
                writeln!(f, "{}", self.env().with(member))?;
            }
            Ok(())
        })
    }
}
