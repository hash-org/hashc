//! Definitions related to parameters to data types, functions, etc.
use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_source::identifier::Identifier;
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

/// An index of a parameter of a parameter list.
///
/// Either a named parameter or a positional one.
#[derive(Debug, Clone, Hash, Copy, PartialEq, Eq, From)]
pub enum ParamIndex {
    /// A named parameter, like `foo(value=3)`.
    Name(Identifier),
    /// A positional parameter, like `dot(x, y)`.
    Position(usize),
}

impl From<ParamId> for ParamIndex {
    fn from(value: ParamId) -> Self {
        ParamIndex::Position(value.1)
    }
}

/// An index of a parameter of a definition parameter list.
///
/// This is a combination of the group index and the parameter index.
/// Group index is
/// ```notrust
/// (a, b)(c, d)(e, f)
/// ^0    ^1    ^2
/// ```
/// and parameter index is [`ParamIndex`].
#[derive(Debug, Clone, Hash, Copy, PartialEq, Eq)]
pub struct DefParamIndex {
    pub group_index: usize,
    pub param_index: ParamIndex,
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
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", self.env().with(param))?;
            }
            Ok(())
        })
    }
}

impl fmt::Display for WithEnv<'_, ParamIndex> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            ParamIndex::Name(name) => write!(f, "{name}"),
            ParamIndex::Position(pos) => write!(f, "{pos}"),
        }
    }
}
