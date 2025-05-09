//! Definitions related to modules.

use std::fmt::Display;

use hash_source::{SourceId, SourceMapUtils, identifier::Identifier};
use hash_storage::{
    get,
    store::{TrivialSequenceStoreKey, statics::StoreId},
};
use textwrap::indent;
use utility_types::Omit;

use crate::{
    intrinsics::{definitions::Intrinsic, make::IsIntrinsic},
    stores::tir_stores,
    tir::{DataDefId, FnDefId, Node, SymbolId},
    tir_node_sequence_store_direct, tir_node_single_store,
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
    /// A module member that is an intrinsic.
    Intrinsic(Intrinsic),
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
            ModMemberValue::Intrinsic(intrinsic) => {
                write!(f, "{}", intrinsic)
            }
        }
    }
}

impl ModMemberValue {
    /// Get the name of the module member.
    pub fn name(&self) -> Option<Identifier> {
        match self {
            ModMemberValue::Data(data_def_id) => get!(*data_def_id, name).value().name,
            ModMemberValue::Mod(mod_def_id) => get!(*mod_def_id, name).value().name,
            ModMemberValue::Fn(fn_def_id) => get!(*fn_def_id, name).value().name,
            ModMemberValue::Intrinsic(intrinsic) => Some(intrinsic.name()),
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
pub struct ModMember {
    pub name: SymbolId,
    pub value: ModMemberValue,
}

tir_node_sequence_store_direct!(ModMember);

/// A module definition.
///
/// This contains a name, parameters, a kind, and a set of members.
#[derive(Debug, Clone, Copy, Omit)]
#[omit(
    arg(ident=ModDefData, fields(id), derive(Debug, Clone, Copy))
)]
pub struct ModDef {
    /// The name of the module.
    pub name: SymbolId,
    /// The kind is parametrised over `params`.
    pub kind: ModKind,
    /// The members of the module.
    pub members: ModMembersId,
}

tir_node_single_store!(ModDef);

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
    pub fn get_mod_member_by_ident(&self, name: impl Into<Identifier>) -> Option<Node<ModMember>> {
        let name = name.into();
        self.members.iter().find_map(|member| {
            if member.borrow().name.borrow().name.is_some_and(|sym| sym == name) {
                Some(member.value())
            } else {
                None
            }
        })
    }
}

impl Display for ModDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let members = (self.members).to_string();
        match self.kind {
            ModKind::ModBlock => {
                write!(f, "mod [name={}, type=block] {{\n{}}}", self.name, indent(&members, "  "))
            }
            ModKind::Source(source) => SourceMapUtils::map(source, |source| {
                write!(
                    f,
                    "mod [name={}, type=file, src=\"{:?}\"] {{\n{}}}",
                    self.name,
                    source.path(),
                    indent(&members, "  ")
                )
            }),
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
        write!(f, "{}", *self.value())
    }
}

impl Display for ModMember {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} := {}", self.name, self.value,)
    }
}

impl Display for ModMemberId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", *self.value())
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
