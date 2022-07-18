//! Error-related data structures for errors that in regards to parameters and
//! arguments within any type that uses parameters.

use std::{collections::HashSet, fmt::Display};

use hash_ast::ast::ParamOrigin;
use hash_source::{identifier::Identifier, location::SourceLocation};

use crate::storage::{
    location::LocationStore,
    primitives::{ArgsId, ParamsId},
    GlobalStorage,
};

/// Particular reason why parameters couldn't be unified, either argument
/// length mis-match or that a name mismatched between the two given parameters.
#[derive(Debug, Clone, Copy)]
pub enum ParamUnificationErrorReason {
    /// The provided and expected parameter lengths mismatched.
    LengthMismatch,
    /// A name mismatch of the parameters occurred at the particular
    /// index.
    NameMismatch(usize),
}

/// This type is used to represent a `source` of where
/// a [super::TcError::ParamGivenTwice] occurs. It can either occur
/// in an argument list, or it can occur within a parameter list.
/// The reporting logic is the same, with the minor wording difference.
#[derive(Debug, Clone)]
pub enum ParamListKind {
    Params(ParamsId),
    Args(ArgsId),
}

impl ParamListKind {
    /// Convert a [ParamListKind] into a [SourceLocation] by looking up the
    /// inner id within the [LocationStore].
    pub(crate) fn to_location(
        &self,
        index: usize,
        store: &LocationStore,
    ) -> Option<SourceLocation> {
        match self {
            ParamListKind::Params(id) => store.get_location((*id, index)),
            ParamListKind::Args(id) => store.get_location((*id, index)),
        }
    }

    /// Get the [ParamOrigin] from the [ParamListKind]
    pub(crate) fn origin(&self, store: &GlobalStorage) -> ParamOrigin {
        match self {
            ParamListKind::Params(id) => store.params_store.get(*id).origin(),
            ParamListKind::Args(id) => store.args_store.get(*id).origin(),
        }
    }

    /// Get the names fields within the [ParamListKind]
    pub(crate) fn names(&self, store: &GlobalStorage) -> HashSet<Identifier> {
        match self {
            ParamListKind::Params(id) => store.params_store.get(*id).names(),
            ParamListKind::Args(id) => store.args_store.get(*id).names(),
        }
    }

    /// Function used to compute the missing fields from another
    /// [ParamListKind]. This does not compute a difference as it doesn't
    /// consider items that are present in the other [ParamListKind] and not
    /// in the current list as `missing`.
    pub(crate) fn compute_missing_fields(
        &self,
        other: Self,
        store: &GlobalStorage,
    ) -> Vec<Identifier> {
        let lhs_names = self.names(store);
        let rhs_names = other.names(store);

        lhs_names.difference(&rhs_names).into_iter().copied().collect()
    }
}

impl Display for ParamListKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParamListKind::Params(_) => write!(f, "fields"),
            ParamListKind::Args(_) => write!(f, "arguments"),
        }
    }
}
