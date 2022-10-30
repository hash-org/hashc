//! Definitions related to parameters to data types, functions, etc.

use hash_utils::{new_sequence_store_key, store::DefaultSequenceStore};

use crate::new::{symbols::Symbol, terms::TermId, types::TyId};

/// A parameter, declaring a potentially named variable with a given type and
/// possibly a default value.
#[derive(Debug, Clone, Hash, Copy)]
pub struct Param {
    pub name: Option<Symbol>,
    pub ty: TyId,
    pub default_value: Option<TermId>,
}

new_sequence_store_key!(pub ParamsId);
pub type ParamsStore = DefaultSequenceStore<ParamsId, Param>;
