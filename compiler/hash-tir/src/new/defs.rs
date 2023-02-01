//! General definition-related utilities

use std::fmt::Display;

use derive_more::From;

use super::{
    data::DataDefId,
    environment::env::{AccessToEnv, WithEnv},
    fns::FnDefId,
    locations::LocationTarget,
    mods::ModDefId,
    scopes::StackId,
};
use crate::new::{symbols::Symbol, terms::TermId, tys::TyId};

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

impl Display for WithEnv<'_, DefId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            DefId::Mod(mod_id) => write!(f, "{}", self.env().with(mod_id)),
            DefId::Data(data_id) => write!(f, "{}", self.env().with(data_id)),
            DefId::Fn(fn_id) => write!(f, "{}", self.env().with(fn_id)),
            DefId::Stack(stack_id) => write!(f, "{}", self.env().with(stack_id)),
        }
    }
}

impl<T> Display for WithEnv<'_, &DefMember<T>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {}{}",
            self.env().with(self.value.name),
            self.env().with(self.value.ty),
            self.value
                .value
                .map(|x| format!(" = {}", self.env().with(x)))
                .unwrap_or_else(|| "".to_string())
        )
    }
}

impl Display for WithEnv<'_, &DefMemberData> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {}{}",
            self.env().with(self.value.name),
            self.env().with(self.value.ty),
            self.value
                .value
                .map(|x| format!(" = {}", self.env().with(x)))
                .unwrap_or_else(|| "".to_string())
        )
    }
}
