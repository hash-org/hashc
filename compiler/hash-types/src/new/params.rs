//! Definitions related to parameters to data types, functions, etc.
use core::fmt;
use std::fmt::Debug;

use hash_utils::{
    new_sequence_store_key,
    store::{CloneStore, DefaultSequenceStore},
};
use utility_types::omit;

use super::environment::env::{AccessToEnv, WithEnv};
use crate::new::{symbols::Symbol, terms::TermId, tys::TyId};

// @@Todo: examples

/// A parameter, declaring a potentially named variable with a given type and
/// possibly a default value.
#[omit(ParamData, [id], [Debug, Clone, Copy])]
#[derive(Debug, Clone, Copy)]
pub struct Param {
    /// The ID of the parameter in the parameter list.
    pub id: ParamId,
    /// The name of the parameter.
    pub name: Option<Symbol>,
    /// The type of the parameter.
    pub ty: TyId,
    /// The default value of the parameter, if given.
    pub default_value: Option<TermId>,
}

new_sequence_store_key!(pub ParamsId);
pub type ParamId = (ParamsId, usize);
pub type ParamsStore = DefaultSequenceStore<ParamsId, Param>;

/// The parameter target of an argument. Either a named parameter or a
/// positional one.
#[derive(Debug, Clone, Hash, Copy)]
pub enum ParamTarget {
    Name(Symbol),
    Position(usize),
}

impl fmt::Display for WithEnv<'_, ParamTarget> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            ParamTarget::Name(name) => todo!(),
            ParamTarget::Position(_) => todo!(),
        }
    }
}
