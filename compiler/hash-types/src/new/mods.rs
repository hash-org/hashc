//! Definitions related to modules.

use hash_source::SourceId;
use hash_utils::{new_sequence_store_key, new_store, new_store_key, store::DefaultSequenceStore};

use crate::new::{
    defs::{DefMember, DefParamsId},
    symbols::Symbol,
    trts::TrtImplData,
};

/// The kind of a module.
#[derive(Debug, Clone, Copy)]
pub enum ModKind {
    /// Defined as a trait implementation.
    ///
    /// Might reference parameters in the mod def.
    TrtImpl(TrtImplData),
    /// Defined as a module (`mod` block).
    ModBlock,
    /// Defined as a file module or interactive.
    Source(SourceId),
}

new_sequence_store_key!(pub ModMembersId);
pub type ModMembersStore = DefaultSequenceStore<ModMembersId, DefMember<ModDefId>>;
pub type ModMemberId = (ModMembersId, usize);

/// A module definition.
///
/// This contains a name, parameters, a kind, and a set of members.
#[derive(Debug, Clone, Copy)]
pub struct ModDef {
    pub name: Symbol,
    pub params: DefParamsId,
    pub kind: ModKind,
    pub members: ModMembersId,

    /// The name of the "Self" type in the scope of the trait definition.
    pub self_type_name: Symbol,
}

new_store_key!(pub ModDefId);
new_store!(pub ModDefStore<ModDefId, ModDef>);
