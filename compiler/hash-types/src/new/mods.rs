//! Definitions related to modules.

use std::fmt::Display;

use hash_source::SourceId;
use hash_utils::{
    new_sequence_store_key, new_store, new_store_key,
    store::{DefaultSequenceStore, SequenceStore, Store},
};
use textwrap::indent;
use utility_types::omit;

use super::{
    data::{DataDefId, DataTy},
    environment::env::{AccessToEnv, WithEnv},
    fns::FnDefId,
};
use crate::new::{defs::DefParamsId, symbols::Symbol};

// @@Todo: examples

/// The subject of an implementation block.
#[derive(Debug, Clone, Copy)]
pub enum ImplSubject {
    Data(DataTy),
    // @@Todo: add some primitives here
}

/// An anonymous implementation
///
/// Contains the subject to implement members on.
#[derive(Debug, Clone, Copy)]
pub struct AnonImpl {
    pub subject: ImplSubject,
}

/// The kind of a module.
///
/// Might reference parameters in the mod def.
#[derive(Debug, Clone, Copy)]
pub enum ModKind {
    /// Defined as an anonymous implementation on a datatype.
    AnonImpl(AnonImpl),
    /// Defined as a module (`mod` block).
    ModBlock,
    /// Defined as a file module or interactive.
    Source(SourceId),
}

/// The right-hand side of a module member definition.
///
/// This can be:
/// - a function definition, e.g  x := () -> i32 => 42;
/// - a data definition, e.g.  x := struct(foo: str);
/// - a module definition, e.g.  x := mod {}, or x := impl y {};
#[derive(Debug, Clone, Copy)]
pub enum ModMemberValue {
    /// A module member that is a definition.
    Data(DataDefId),
    /// A module member that is a nested module.
    Mod(ModDefId),
    /// A module member that is a function.
    Fn(FnDefId),
    // @@Future: constants
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

    /// The parameters of the module, if any.
    pub params: DefParamsId,

    /// The kind is parametrised over `params`.
    pub kind: ModKind,

    /// The members of the module.
    pub members: ModMembersId,

    /// The name of the "Self" type in the scope of the trait definition, if
    /// present.
    pub self_ty_name: Option<Symbol>,
}

new_store_key!(pub ModDefId);
new_store!(pub ModDefStore<ModDefId, ModDef>);

impl Display for WithEnv<'_, &ModDef> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let members = self.env().with(self.value.members).to_string();
        match self.value.kind {
            ModKind::AnonImpl(_) => todo!(),
            ModKind::ModBlock => {
                write!(
                    f,
                    "mod [name={}, type=block] {} {{\n{}}}",
                    self.env().with(self.value.name),
                    self.env().with(self.value.params),
                    indent(&members, "  ")
                )
            }
            ModKind::Source(source_id) => {
                let source_name = self.env().source_map().source_name(source_id);
                write!(
                    f,
                    "mod [name={}, type=file, src=\"{source_name}\"] {} {{\n{}}}",
                    self.env().with(self.value.name),
                    self.env().with(self.value.params),
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

impl Display for WithEnv<'_, ModMemberValue> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            ModMemberValue::Data(data_def_id) => write!(f, "{}", self.env().with(data_def_id)),
            ModMemberValue::Mod(mod_def_id) => write!(f, "{}", self.env().with(mod_def_id)),
            ModMemberValue::Fn(fn_def_id) => write!(f, "{}", self.env().with(fn_def_id)),
        }
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
