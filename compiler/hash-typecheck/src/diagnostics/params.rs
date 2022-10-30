//! Error-related data structures for errors that in regards to parameters and
//! arguments within any type that uses parameters.

use std::fmt::Display;

use hash_types::{arguments::ArgsIdOld, params::ParamsId, pats::PatArgsId};
use hash_utils::store::SequenceStoreKey;

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
    Args(ArgsIdOld),
}

impl ParamListKind {
    /// Get the length of the inner stored parameter.
    pub(crate) fn len(&self) -> usize {
        match self {
            ParamListKind::Params(id) => id.len(),
            ParamListKind::PatArgs(id) => id.len(),
            ParamListKind::Args(id) => id.len(),
        }
    }

    /// Get the English subject noun of the [ParamListKind]
    pub(crate) fn as_noun(&self) -> &'static str {
        match self {
            ParamListKind::PatArgs(_) | ParamListKind::Params(_) => "field",
            ParamListKind::Args(_) => "argument",
        }
    }
}

impl Display for ParamListKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}s", self.as_noun())
    }
}
