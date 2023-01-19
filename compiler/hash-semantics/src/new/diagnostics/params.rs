//! Error-related data structures for errors that in regards to parameters and
//! arguments within any type that uses parameters.

use hash_tir::new::{
    args::{ArgsId, PatArgsId},
    defs::{DefArgsId, DefParamsId, DefPatArgsId},
    locations::IndexedLocationTarget,
    params::ParamsId,
};
use hash_utils::store::SequenceStoreKey;

/// This type is used to represent a `source` of where
/// a [`TcError`] occurs when it relates to parameters or
/// arguments. It can either occur in an argument list, or it can occur within a
/// parameter list. The reporting logic is the same, with the minor wording
/// difference.
#[derive(Debug, Clone, Copy)]
pub enum SomeArgsId {
    /// Occurs when trying to unify two lists of parameters.
    Params(ParamsId),
    /// Occurs when trying to unify pattern arguments with parameters.
    PatArgs(PatArgsId),
    /// Occurs when trying to unify term arguments with parameters.
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

/// This type is used to represent a `source` of where
/// a [`TcError`] occurs when it relates to groups of parameters or
/// arguments.
#[derive(Debug, Clone, Copy)]
pub enum SomeDefArgsId {
    /// Occurs when trying to unify two lists of definition parameters.
    Params(DefParamsId),
    /// Occurs when trying to unify pattern arguments with parameters.
    PatArgs(DefPatArgsId),
    /// Occurs when trying to unify term arguments with parameters.
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
