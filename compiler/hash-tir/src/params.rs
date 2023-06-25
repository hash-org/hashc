//! Definitions related to parameters to data types, functions, etc.
use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_source::identifier::Identifier;
use hash_utils::{
    new_sequence_store_key,
    store::{DefaultSequenceStore, SequenceStore, SequenceStoreKey},
};
use utility_types::omit;

use super::{
    args::{ArgsId, PatArgsId},
    environment::env::{AccessToEnv, WithEnv},
    locations::IndexedLocationTarget,
    terms::TermId,
};
use crate::{impl_sequence_store_id, symbols::Symbol, tys::TyId};

// @@Todo: examples

/// A parameter, declaring a potentially named variable with a given type and
/// possibly a default value.
#[derive(Debug, Clone, Copy)]
#[omit(ParamData, [id], [Debug, Clone, Copy])]
pub struct Param {
    /// The ID of the parameter in the parameter list.
    pub id: ParamId,
    /// The name of the parameter.
    pub name: Symbol,
    /// The type of the parameter.
    pub ty: TyId,
    /// The default value of the parameter.
    pub default: Option<TermId>,
}

impl From<Param> for ParamData {
    fn from(value: Param) -> Self {
        ParamData { name: value.name, ty: value.ty, default: value.default }
    }
}

new_sequence_store_key!(pub ParamsId);
pub type ParamId = (ParamsId, usize);
pub type ParamsStore = DefaultSequenceStore<ParamsId, Param>;
impl_sequence_store_id!(ParamsId, Param, params);

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

impl fmt::Display for WithEnv<'_, &Param> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {}{}",
            self.env().with(self.value.name),
            self.env().with(self.value.ty),
            if let Some(default) = self.value.default {
                format!(" = {}", self.env().with(default))
            } else {
                "".to_string()
            }
        )
    }
}

/// Some kind of parameters or arguments, either [`ParamsId`], [`PatArgsId`] or
/// [`ArgsId`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub enum SomeParamsOrArgsId {
    Params(ParamsId),
    PatArgs(PatArgsId),
    Args(ArgsId),
}

impl SomeParamsOrArgsId {
    /// Get the length of the inner stored parameters.
    pub fn len(&self) -> usize {
        match self {
            SomeParamsOrArgsId::Params(id) => id.len(),
            SomeParamsOrArgsId::PatArgs(id) => id.len(),
            SomeParamsOrArgsId::Args(id) => id.len(),
        }
    }

    /// Whether the inner stored parameters list is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the English subject noun of the [SomeParamsOrArgsId]
    pub fn as_str(&self) -> &'static str {
        match self {
            SomeParamsOrArgsId::Params(_) => "parameters",
            SomeParamsOrArgsId::PatArgs(_) => "pattern arguments",
            SomeParamsOrArgsId::Args(_) => "arguments",
        }
    }
}

impl From<SomeParamsOrArgsId> for IndexedLocationTarget {
    fn from(target: SomeParamsOrArgsId) -> Self {
        match target {
            SomeParamsOrArgsId::Params(id) => IndexedLocationTarget::Params(id),
            SomeParamsOrArgsId::PatArgs(id) => IndexedLocationTarget::PatArgs(id),
            SomeParamsOrArgsId::Args(id) => IndexedLocationTarget::Args(id),
        }
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

impl fmt::Display for ParamIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParamIndex::Name(name) => write!(f, "{name}"),
            ParamIndex::Position(pos) => write!(f, "{pos}"),
        }
    }
}

impl fmt::Display for WithEnv<'_, ParamIndex> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl fmt::Display for WithEnv<'_, SomeParamsOrArgsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            SomeParamsOrArgsId::Params(id) => write!(f, "{}", self.env().with(id)),
            SomeParamsOrArgsId::PatArgs(id) => write!(f, "{}", self.env().with(id)),
            SomeParamsOrArgsId::Args(id) => write!(f, "{}", self.env().with(id)),
        }
    }
}
