//! Definitions related to arguments to data structures, functions,
//! etc.
use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_utils::{
    itertools::Itertools,
    store::{SequenceStore, SequenceStoreKey, TrivialSequenceStoreKey},
};
use utility_types::omit;

use super::{
    locations::{IndexedLocationTarget, LocationTarget},
    params::ParamIndex,
    pats::PatId,
};
use crate::{
    environment::stores::{SequenceStoreValue, SingleStoreValue, StoreId},
    params::ParamsId,
    terms::{Term, TermId},
    tir_debug_value_of_sequence_store_element_id, tir_sequence_store_direct,
};

/// An argument to a parameter.
///
/// This might be used for arguments in constructor calls `C(...)`, function
/// calls `f(...)` or `f<...>`, or type arguments.
#[omit(ArgData, [id], [Debug, Clone, Copy])]
#[derive(Debug, Clone, Copy)]
pub struct Arg {
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

tir_sequence_store_direct!(
    store = pub ArgsStore,
    id = pub ArgsId[ArgId],
    value = Arg,
    store_name = args
);

tir_debug_value_of_sequence_store_element_id!(ArgId);

impl Arg {
    /// From the given parameters, create arguments that directly refer to the
    /// parameters using `Term::Var`.
    ///
    /// Example:
    /// ```notrust
    /// X := datatype <A: Type, B: Type, C: Type> { foo: () -> X<A, B, C> }
    ///                                                         ^^^^^^^^^ this is what this function creates
    /// ```
    pub fn seq_from_param_names_as_vars(params_id: ParamsId) -> ArgsId {
        Arg::seq(
            // For each parameter, create an argument referring to it
            params_id
                .iter()
                .enumerate()
                .map(|(i, param)| {
                    move |_| Arg {
                        target: ParamIndex::Position(i),
                        value: Term::create(Term::Var(param.borrow().name)),
                    }
                })
                .collect_vec(),
        )
    }
}

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
#[derive(Debug, Clone, Copy, From, PartialEq, Eq)]
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

tir_sequence_store_direct!(
    store = pub PatArgsStore,
    id = pub PatArgsId[PatArgId],
    value = PatArg,
    store_name = pat_args
);

tir_debug_value_of_sequence_store_element_id!(PatArgId);

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
    type ElementKey = (SomeArgsId, usize);

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
            SomeArgId(SomeArgsId::PatArgs(id), index) => {
                LocationTarget::PatArg(PatArgId(id, index))
            }
            SomeArgId(SomeArgsId::Args(id), index) => LocationTarget::Arg(ArgId(id, index)),
        }
    }
}

impl fmt::Display for SomeArgsId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SomeArgsId::Args(id) => write!(f, "{}", id),
            SomeArgsId::PatArgs(id) => write!(f, "{}", id),
        }
    }
}

impl fmt::Display for Arg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.target {
            ParamIndex::Name(name) => {
                write!(f, "{} = {}", name, self.value)
            }
            ParamIndex::Position(_) => write!(f, "{}", self.value),
        }
    }
}

impl fmt::Display for ArgId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl fmt::Display for ArgsId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, arg) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        Ok(())
    }
}

impl fmt::Display for PatOrCapture {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatOrCapture::Pat(pat) => {
                write!(f, "{}", pat)
            }
            PatOrCapture::Capture => {
                write!(f, "_")
            }
        }
    }
}

impl fmt::Display for PatArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.target {
            ParamIndex::Name(name) => {
                write!(f, "{} = {}", name, self.pat)
            }
            ParamIndex::Position(_) => write!(f, "{}", self.pat),
        }
    }
}

impl fmt::Display for PatArgId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl fmt::Display for PatArgsId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, pat_arg) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", pat_arg)?;
        }
        Ok(())
    }
}
