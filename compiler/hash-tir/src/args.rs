//! Definitions related to arguments to data structures, functions,
//! etc.
use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_utils::{
    new_sequence_store_key,
    store::{DefaultSequenceStore, SequenceStore, SequenceStoreKey},
};
use utility_types::omit;

use super::{
    environment::env::{AccessToEnv, WithEnv},
    locations::{IndexedLocationTarget, LocationTarget},
    params::ParamIndex,
    pats::PatId,
};
use crate::{impl_sequence_store_id, terms::TermId};

/// An argument to a parameter.
///
/// This might be used for arguments in constructor calls `C(...)`, function
/// calls `f(...)` or `f<...>`, or type arguments.
#[omit(ArgData, [id], [Debug, Clone, Copy])]
#[derive(Debug, Clone, Copy)]
pub struct Arg {
    /// The ID of the argument in the argument list.
    pub id: ArgId,
    /// Argument target (named or positional), if known.
    pub target: ParamIndex,
    /// The term that is the value of the argument.
    pub value: TermId,
}

impl From<Arg> for ArgData {
    fn from(value: Arg) -> Self {
        ArgData { target: value.target, value: value.value }
    }
}

new_sequence_store_key!(pub ArgsId);
pub type ArgId = (ArgsId, usize);
pub type ArgsStore = DefaultSequenceStore<ArgsId, Arg>;

impl_sequence_store_id!(ArgsId, Arg, args);

/// A pattern or a capture.
///
/// A capture exists in pattern lists and pattern arguments, and is used to
/// indicate that this field is captured by a spread pattern in the aggregate.
///
/// Initially, no pattern arguments are captures, instead the `spread` member in
/// pattern lists denotes where the spread is located. Then, the list is
/// reordered to match the target parameter list, which involves making some
/// slots into `PatOrCapture::Capture` to indicate that the corresponding
/// parameter is captured by the spread. After that point the spread is no
/// longer needed (other than for errors).
#[derive(Debug, Clone, Copy, From)]
pub enum PatOrCapture {
    /// A pattern.
    Pat(PatId),
    /// A capture.
    Capture,
}

impl PatOrCapture {
    /// Used for or-patterns which use a `PatListId` but contain no captures.
    pub fn assert_pat(self) -> PatId {
        match self {
            PatOrCapture::Pat(pat) => pat,
            PatOrCapture::Capture => panic!("Expected a pattern, got a capture"),
        }
    }
}

/// A pattern argument to a parameter
///
/// This might be used for constructor patterns like `C(true, x)`.
#[omit(PatArgData, [id], [Debug, Clone, Copy])]
#[derive(Debug, Clone, Copy)]
pub struct PatArg {
    /// The ID of the argument in the argument pattern list.
    pub id: PatArgId,
    /// Argument target (named or positional).
    pub target: ParamIndex,
    /// The pattern in place for this argument.
    pub pat: PatOrCapture,
}

impl From<PatArg> for PatArgData {
    fn from(value: PatArg) -> Self {
        PatArgData { target: value.target, pat: value.pat }
    }
}

new_sequence_store_key!(pub PatArgsId);
pub type PatArgId = (PatArgsId, usize);
pub type PatArgsStore = DefaultSequenceStore<PatArgsId, PatArg>;
impl_sequence_store_id!(PatArgsId, PatArg, pat_args);

/// Some kind of arguments, either [`PatArgsId`] or [`ArgsId`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub enum SomeArgsId {
    PatArgs(PatArgsId),
    Args(ArgsId),
}

/// An index into a `SomeArgsId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub struct SomeArgId(pub SomeArgsId, pub usize);

impl SequenceStoreKey for SomeArgsId {
    fn to_index_and_len(self) -> (usize, usize) {
        match self {
            SomeArgsId::PatArgs(id) => id.to_index_and_len(),
            SomeArgsId::Args(id) => id.to_index_and_len(),
        }
    }

    fn from_index_and_len_unchecked(index: usize, len: usize) -> Self {
        SomeArgsId::Args(ArgsId::from_index_and_len_unchecked(index, len))
    }
}

impl From<ArgId> for SomeArgId {
    fn from(val: ArgId) -> Self {
        SomeArgId(SomeArgsId::Args(val.0), val.1)
    }
}

impl From<PatArgId> for SomeArgId {
    fn from(val: PatArgId) -> Self {
        SomeArgId(SomeArgsId::PatArgs(val.0), val.1)
    }
}

impl From<SomeArgsId> for IndexedLocationTarget {
    fn from(val: SomeArgsId) -> Self {
        match val {
            SomeArgsId::PatArgs(id) => IndexedLocationTarget::PatArgs(id),
            SomeArgsId::Args(id) => IndexedLocationTarget::Args(id),
        }
    }
}

impl From<SomeArgId> for LocationTarget {
    fn from(val: SomeArgId) -> Self {
        match val {
            SomeArgId(SomeArgsId::PatArgs(id), index) => LocationTarget::PatArg((id, index)),
            SomeArgId(SomeArgsId::Args(id), index) => LocationTarget::Arg((id, index)),
        }
    }
}

impl fmt::Display for WithEnv<'_, SomeArgsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            SomeArgsId::Args(id) => write!(f, "{}", self.env().with(id)),
            SomeArgsId::PatArgs(id) => write!(f, "{}", self.env().with(id)),
        }
    }
}

impl fmt::Display for WithEnv<'_, &Arg> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value.target {
            ParamIndex::Name(name) => {
                write!(f, "{} = {}", name, self.env().with(self.value.value))
            }
            ParamIndex::Position(_) => write!(f, "{}", self.env().with(self.value.value)),
        }
    }
}

impl fmt::Display for WithEnv<'_, ArgId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.env().with(&self.stores().args().get_element(self.value)))
    }
}

impl fmt::Display for WithEnv<'_, ArgsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().args().map_fast(self.value, |args| {
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", self.env().with(arg))?;
            }
            Ok(())
        })
    }
}

impl fmt::Display for WithEnv<'_, PatOrCapture> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            PatOrCapture::Pat(pat) => {
                write!(f, "{}", self.env().with(pat))
            }
            PatOrCapture::Capture => {
                write!(f, "_")
            }
        }
    }
}

impl fmt::Display for WithEnv<'_, &PatArg> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value.target {
            ParamIndex::Name(name) => {
                write!(f, "{} = {}", name, self.env().with(self.value.pat))
            }
            ParamIndex::Position(_) => write!(f, "{}", self.env().with(self.value.pat)),
        }
    }
}

impl fmt::Display for WithEnv<'_, PatArgId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.env().with(&self.stores().pat_args().get_element(self.value)))
    }
}

impl fmt::Display for WithEnv<'_, PatArgsId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().pat_args().map_fast(self.value, |pat_args| {
            for (i, pat_arg) in pat_args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", self.env().with(pat_arg))?;
            }
            Ok(())
        })
    }
}
