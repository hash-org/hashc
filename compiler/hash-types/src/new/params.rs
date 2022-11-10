//! Definitions related to parameters to data types, functions, etc.
use core::fmt;
use std::fmt::Debug;

use hash_utils::{
    new_sequence_store_key,
    store::{DefaultSequenceStore, SequenceStore},
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
    pub name: Symbol,
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

impl fmt::Display for WithEnv<'_, &Param> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {}{}",
            self.env().with(self.value.name),
            self.env().with(self.value.ty),
            if let Some(default_value) = self.value.default_value {
                format!(" = {}", self.env().with(default_value))
            } else {
                "".to_string()
            }
        )
    }
}

impl fmt::Display for WithEnv<'_, ParamId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.env().with(&self.stores().params().get_element(self.value)))
    }
}

impl fmt::Display for WithEnv<'_, ParamsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().params().map_fast(self.value, |params| {
            for (i, param) in params.iter().enumerate() {
                write!(f, "{}", self.env().with(param))?;
                if i > 0 {
                    write!(f, ", ")?;
                }
            }
            Ok(())
        })
    }
}

impl fmt::Display for WithEnv<'_, ParamTarget> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            ParamTarget::Name(name) => write!(f, "{}", self.env().with(name)),
            ParamTarget::Position(pos) => write!(f, "{pos}"),
        }
    }
}
