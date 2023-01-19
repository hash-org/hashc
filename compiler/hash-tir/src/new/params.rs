//! Definitions related to parameters to data types, functions, etc.
use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_source::identifier::Identifier;
use hash_utils::{
    new_sequence_store_key,
    store::{DefaultSequenceStore, SequenceStore, SequenceStoreKey, Store},
};
use utility_types::omit;

use super::{
    args::{ArgsId, PatArgsId},
    defs::{DefArgsId, DefParamsId, DefPatArgsId},
    environment::env::{AccessToEnv, WithEnv},
    locations::IndexedLocationTarget,
};
use crate::new::{symbols::Symbol, terms::TermId, tys::TyId};

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
            "{}{}{}",
            self.stores().symbol().map_fast(self.value.name, |sym| {
                match (sym.name, self.value.default_value) {
                    (None, None) => "".to_string(),
                    (Some(name), _) => format!("{name}: "),
                    (_, _) => "_: ".to_string(),
                }
            }),
            self.env().with(self.value.ty),
            if let Some(default_value) = self.value.default_value {
                format!(" = {}", self.env().with(default_value))
            } else {
                "".to_string()
            }
        )
    }
}

/// Some kind of arguments, either [`ParamsId`], [`PatArgsId`] or [`ArgsId`].
#[derive(Debug, Clone, Copy)]
pub enum SomeArgsId {
    Params(ParamsId),
    PatArgs(PatArgsId),
    Args(ArgsId),
}

impl SomeArgsId {
    /// Get the length of the inner stored parameters.
    pub fn len(&self) -> usize {
        match self {
            SomeArgsId::Params(id) => id.len(),
            SomeArgsId::PatArgs(id) => id.len(),
            SomeArgsId::Args(id) => id.len(),
        }
    }

    /// Whether the inner stored parameters list is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the English subject noun of the [SomeArgsId]
    pub fn as_str(&self) -> &'static str {
        match self {
            SomeArgsId::Params(_) => "parameters",
            SomeArgsId::PatArgs(_) => "pattern arguments",
            SomeArgsId::Args(_) => "arguments",
        }
    }
}

impl From<SomeArgsId> for IndexedLocationTarget {
    fn from(target: SomeArgsId) -> Self {
        match target {
            SomeArgsId::Params(id) => IndexedLocationTarget::Params(id),
            SomeArgsId::PatArgs(id) => IndexedLocationTarget::PatArgs(id),
            SomeArgsId::Args(id) => IndexedLocationTarget::Args(id),
        }
    }
}

/// Some kind of definition arguments, either [`DefParamsId`], [`DefPatArgsId`]
/// or [`DefArgsId`].
#[derive(Debug, Clone, Copy)]
pub enum SomeDefArgsId {
    Params(DefParamsId),
    PatArgs(DefPatArgsId),
    Args(DefArgsId),
}

impl SomeDefArgsId {
    /// Get the length of the inner stored parameter group list.
    pub fn len(&self) -> usize {
        match self {
            SomeDefArgsId::Params(id) => id.len(),
            SomeDefArgsId::PatArgs(id) => id.len(),
            SomeDefArgsId::Args(id) => id.len(),
        }
    }

    /// Whether the inner stored parameter group list is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the English subject noun of the [SomeDefArgsId]
    pub fn as_str(&self) -> &'static str {
        match self {
            SomeDefArgsId::Params(_) => "parameter groups",
            SomeDefArgsId::PatArgs(_) => "pattern argument groups",
            SomeDefArgsId::Args(_) => "argument groups",
        }
    }
}

impl From<SomeDefArgsId> for IndexedLocationTarget {
    fn from(target: SomeDefArgsId) -> Self {
        match target {
            SomeDefArgsId::Params(id) => IndexedLocationTarget::DefParams(id),
            SomeDefArgsId::PatArgs(id) => IndexedLocationTarget::DefPatArgs(id),
            SomeDefArgsId::Args(id) => IndexedLocationTarget::DefArgs(id),
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

impl fmt::Display for WithEnv<'_, ParamIndex> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            ParamIndex::Name(name) => write!(f, "{name}"),
            ParamIndex::Position(pos) => write!(f, "{pos}"),
        }
    }
}

impl fmt::Display for WithEnv<'_, SomeArgsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            SomeArgsId::Params(id) => write!(f, "{}", self.env().with(id)),
            SomeArgsId::PatArgs(id) => write!(f, "{}", self.env().with(id)),
            SomeArgsId::Args(id) => write!(f, "{}", self.env().with(id)),
        }
    }
}
