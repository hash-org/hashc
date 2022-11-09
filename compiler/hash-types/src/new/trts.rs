//! Definitions related to traits.

use std::fmt::Display;

use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{DefaultSequenceStore, DefaultStore, SequenceStore, Store},
};
use textwrap::indent;
use utility_types::omit;

use super::environment::env::{AccessToEnv, WithEnv};
use crate::new::{
    defs::{DefArgsId, DefMember, DefParamsId},
    symbols::Symbol,
};

new_sequence_store_key!(pub TrtMembersId);
pub type TrtMembersStore = DefaultSequenceStore<TrtMembersId, DefMember<TrtMembersId>>;
pub type TrtMemberId = (TrtMembersId, usize);

// @@Todo: examples

/// A trait definition.
///
/// Includes a name, a set of parameters for the trait, as well as a set of
/// members, as well as the name of "Self".
#[derive(Debug, Clone, Copy)]
#[omit(TrtDefData, [id], [Debug, Clone, Copy])]
pub struct TrtDef {
    pub id: TrtDefId,
    pub name: Symbol,
    pub params: DefParamsId,
    pub members: TrtMembersId,

    /// The name of the "Self" type in the scope of the trait definition.
    pub self_ty_name: Symbol,
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

impl Display for WithEnv<'_, TrtDefId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.stores().trt_def().map_fast(self.value, |def| write!(f, "{}", self.env().with(def)))
    }
}

impl Display for WithEnv<'_, TrtMembersId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.stores().trt_members().map_fast(self.value, |members| {
            for member in members.iter() {
                writeln!(f, "{}", self.env().with(member))?;
            }
            Ok(())
        })
    }
}

impl Display for WithEnv<'_, &TrtDef> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.env().stores();
        let members = self.env().with(self.value.members).to_string();
        write!(f, "trait {{\n{}\n}}", indent(&members, "    "))
    }
}
