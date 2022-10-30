//! Contains structures to keep track of traits and information relating to
//! them.
use std::fmt;

use hash_source::identifier::Identifier;
use hash_utils::{
    new_sequence_store_key, new_store, new_store_key,
    store::{CloneStore, DefaultSequenceStore, DefaultStore},
};

use crate::{
    defs::{DefArgsId, DefMember, DefParamsId},
    fmt::{ForFormatting, PrepareForFormatting},
    scope::ScopeId,
    symbols::Symbol,
};

// -- OLD --
/// A trait definition, containing a binding name and a set of constant members.
#[derive(Debug, Clone, Copy)]
pub struct TrtDefOld {
    pub name: Option<Identifier>,
    pub members: ScopeId,
}

new_store_key!(pub TrtDefIdOld);
new_store!(pub TrtDefStoreOld<TrtDefIdOld, TrtDefOld>);

impl PrepareForFormatting for TrtDefIdOld {}

impl fmt::Display for ForFormatting<'_, TrtDefIdOld> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let trt_def_id = self.t;

        match self.global_storage.trt_def_store.get(trt_def_id).name {
            Some(name) if !self.opts.expand => {
                write!(f, "{name}")
            }
            _ => {
                write!(f, "trait {{..}}")
            }
        }
    }
}

// -- NEW --

new_sequence_store_key!(pub TrtMembersId);
pub type TrtMembersStore = DefaultSequenceStore<TrtMembersId, DefMember<TrtDefId>>;
pub type TrtMemberId = (TrtMembersId, usize);

/// A trait definition.
///
/// Includes a name, a set of parameters for the trait, as well as a set of
/// members, as well as the name of "Self".
#[derive(Debug, Clone, Copy)]
pub struct TrtDef {
    pub name: Identifier,
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
