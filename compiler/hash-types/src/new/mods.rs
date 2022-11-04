//! Definitions related to modules.

use hash_source::SourceId;
use hash_utils::{new_sequence_store_key, new_store, new_store_key, store::DefaultSequenceStore};
use utility_types::omit;

use super::{data::DataTy, trts::TrtBound};
use crate::new::{
    defs::{DefMember, DefParamsId},
    symbols::Symbol,
};

// @@Todo: examples

/// The subject of an implementation block.
#[derive(Debug, Clone, Copy)]
pub enum ImplSubject {
    Data(DataTy),
    // @@Todo: add some primitives here
}

/// A trait implementation
///
/// Contains a trait bound to implement, as well as the subject to implement
/// it on.
#[derive(Debug, Clone, Copy)]
pub struct TrtImpl {
    pub subject: ImplSubject,
    pub trt: TrtBound,
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
    /// Defined as a trait implementation.
    TrtImpl(TrtImpl),
    /// Defined as an anonymous implementation on a datatype.
    AnonImpl(AnonImpl),
    /// Defined as a module (`mod` block).
    ModBlock,
    /// Defined as a file module or interactive.
    Source(SourceId),
}

new_sequence_store_key!(pub ModMembersId);
pub type ModMembersStore = DefaultSequenceStore<ModMembersId, DefMember<ModMembersId>>;
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
