//! Definitions related to traits.

use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{DefaultSequenceStore, DefaultStore},
};

use crate::new::{
    defs::{DefArgsId, DefMember, DefParamsId},
    symbols::Symbol,
};

new_sequence_store_key!(pub TrtMembersId);
pub type TrtMembersStore = DefaultSequenceStore<TrtMembersId, DefMember<TrtDefId>>;
pub type TrtMemberId = (TrtMembersId, usize);

/// A trait definition.
///
/// Includes a name, a set of parameters for the trait, as well as a set of
/// members, as well as the name of "Self".
#[derive(Debug, Clone, Copy)]
pub struct TrtDef {
    pub name: Symbol,
    pub params: DefParamsId,
    pub members: TrtMembersId,

    /// The name of the "Self" type in the scope of the trait definition.
    pub self_type_name: Symbol,
}
new_store_key!(pub TrtDefId);
pub type TrtDefStore = DefaultStore<TrtDefId, TrtDef>;

/// A trait bound.
///
/// Includes a trait definition, and a set of arguments for the trait.
#[derive(Debug, Clone, Copy)]
pub struct TrtBound {
    pub trt: TrtDefId,
    pub args: DefArgsId,
}
new_sequence_store_key!(pub TrtBoundsId);
pub type TrtBoundsStore = DefaultSequenceStore<TrtBoundsId, TrtBound>;
