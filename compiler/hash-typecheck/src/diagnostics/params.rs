//! Error-related data structures for errors that in regards to parameters and
//! arguments within any type that uses parameters.

use std::{collections::HashSet, fmt::Display};

use hash_ast::ast::ParamOrigin;
use hash_source::{identifier::Identifier, location::SourceLocation};

use crate::storage::{
    arguments::ArgsId, location::LocationStore, params::ParamsId, pats::PatArgsId,
    primitives::GetNameOpt, GlobalStorage,
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
/// a [super::error::TcError::ParamGivenTwice] occurs. It can either occur
/// in an argument list, or it can occur within a parameter list.
/// The reporting logic is the same, with the minor wording difference.
#[derive(Debug, Clone, Copy)]
pub enum ParamListKind {
    Params(ParamsId),
    PatArgs(PatArgsId),
    Args(ArgsId),
}

impl ParamListKind {
    /// Convert a [ParamListKind] and a field index into a [SourceLocation] by
    /// looking up the inner id within the [LocationStore].
    pub(crate) fn field_location(
        &self,
        index: usize,
        store: &LocationStore,
    ) -> Option<SourceLocation> {
        match self {
            ParamListKind::Params(id) => store.get_location((*id, index)),
            ParamListKind::PatArgs(id) => store.get_location((*id, index)),
            ParamListKind::Args(id) => store.get_location((*id, index)),
        }
    }

    /// Get the length of the inner stored parameter.
    pub(crate) fn len(&self, store: &GlobalStorage) -> usize {
        match self {
            ParamListKind::Params(id) => store.params_store.get_size(*id),
            ParamListKind::PatArgs(id) => store.pat_args_store.get_size(*id),
            ParamListKind::Args(id) => store.args_store.get_size(*id),
        }
    }

    /// Get the [ParamOrigin] from the [ParamListKind]
    pub(crate) fn origin(&self, store: &GlobalStorage) -> ParamOrigin {
        match self {
            ParamListKind::Params(id) => store.params_store.get_origin(*id),
            ParamListKind::PatArgs(id) => store.pat_args_store.get_origin(*id),
            ParamListKind::Args(id) => store.args_store.get_origin(*id),
        }
    }

    /// Get the names fields within the [ParamListKind]
    pub(crate) fn names(&self, store: &GlobalStorage) -> HashSet<Identifier> {
        match self {
            ParamListKind::Params(id) => store.params_store.names(*id),
            ParamListKind::PatArgs(id) => store.pat_args_store.names(*id),
            ParamListKind::Args(id) => store.args_store.names(*id),
        }
    }

    /// Get a stored parameter/field by name.
    pub(crate) fn get_name_index(&self, name: Identifier, store: &GlobalStorage) -> Option<usize> {
        match self {
            ParamListKind::Params(id) => {
                store.params_store.get_by_name(*id, name).map(|param| param.0)
            }
            ParamListKind::PatArgs(id) => {
                store.pat_args_store.get_by_name(*id, name).map(|param| param.0)
            }
            ParamListKind::Args(id) => store.args_store.get_by_name(*id, name).map(|param| param.0),
        }
    }

    /// Function used to compute the missing fields from another
    /// [ParamListKind]. This does not compute a difference as it doesn't
    /// consider items that are present in the other [ParamListKind] and not
    /// in the current list as `missing`.
    pub(crate) fn compute_missing_fields(
        &self,
        other: &Self,
        store: &GlobalStorage,
    ) -> Vec<Identifier> {
        let lhs_names = self.names(store);
        let rhs_names = other.names(store);

        lhs_names.difference(&rhs_names).into_iter().copied().collect()
    }

    /// Get the English subject noun of the [ParamListKind]
    pub(crate) fn as_noun(&self) -> &'static str {
        match self {
            ParamListKind::PatArgs(_) | ParamListKind::Params(_) => "field",
            ParamListKind::Args(_) => "argument",
        }
    }
}

impl GetNameOpt for ParamListKind {
    fn get_name_opt(&self) -> Option<Identifier> {
        todo!()
    }
}

impl Display for ParamListKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}s", self.as_noun())
    }
}
