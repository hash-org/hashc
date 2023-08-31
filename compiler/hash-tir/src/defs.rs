//! General definition-related utilities

use std::fmt::Display;

use hash_utils::derive_more::From;

use super::{
    data::DataDefId, fns::FnDefId, locations::LocationTarget, mods::ModDefId, scopes::StackId,
};
use crate::{symbols::Symbol, terms::TermId, tys::TyId};

/// A member of a definition.
///
/// A definition might be a trait, impl block, or a module.
///
/// Includes a name, the original definition ID, an index into the original
/// definition's members, as well as the type of the member, and an optional
/// value of the member.
#[derive(Debug, Clone, Copy)]
pub struct DefMember<OriginalDefMembersId> {
    pub id: (OriginalDefMembersId, usize),
    pub name: Symbol,
    pub ty: TyId,
    pub value: Option<TermId>,
}

/// The data version of [`DefMember`] (i.e. without ID).
#[derive(Debug, Clone, Copy)]
pub struct DefMemberData {
    pub name: Symbol,
    pub ty: TyId,
    pub value: Option<TermId>,
}

/// The ID of some definition.
///
/// This is used to refer to a definition in a generic way, without knowing
/// what kind of definition it is.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
pub enum DefId {
    Mod(ModDefId),
    Data(DataDefId),
    Fn(FnDefId),
    Stack(StackId),
}

impl From<DefId> for LocationTarget {
    fn from(def_id: DefId) -> Self {
        match def_id {
            DefId::Mod(mod_id) => LocationTarget::ModDef(mod_id),
            DefId::Data(data_id) => LocationTarget::DataDef(data_id),
            DefId::Fn(fn_id) => LocationTarget::FnDef(fn_id),
            DefId::Stack(stack_id) => LocationTarget::Stack(stack_id),
        }
    }
}

impl Display for DefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DefId::Mod(mod_id) => write!(f, "{}", mod_id),
            DefId::Data(data_id) => write!(f, "{}", data_id),
            DefId::Fn(fn_id) => write!(f, "{}", fn_id),
            DefId::Stack(stack_id) => write!(f, "{}", stack_id),
        }
    }
}

impl<T> Display for DefMember<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {}{}",
            self.name,
            self.ty,
            self.value.map(|x| format!(" = {}", x)).unwrap_or_default()
        )
    }
}

impl Display for DefMemberData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {}{}",
            self.name,
            self.ty,
            self.value.map(|x| format!(" = {}", x)).unwrap_or_default()
        )
    }
}
