//! Definitions related to patterns.

use core::fmt;

use derive_more::From;
use hash_ast::ast::RangeEnd;
use hash_utils::{
    new_sequence_store_key, new_store, new_store_key,
    store::{CloneStore, DefaultSequenceStore, SequenceStore, Store},
};

use super::{
    args::{PatArgsId, PatOrCapture},
    control::{IfPat, OrPat},
    data::CtorPat,
    environment::env::{AccessToEnv, WithEnv},
    lits::{ArrayPat, LitPat},
    scopes::{BindingPat, StackMemberId},
    symbols::Symbol,
    tuples::TuplePat,
};

/// A spread "pattern" (not part of [`Pat`]), which can appear in list patterns,
/// tuple patterns, and constructor patterns.
#[derive(Copy, Clone, Debug)]
pub struct Spread {
    /// The name of the spread bind.
    /// If `name` does not map to a specific `Identifier` name, it means
    /// that the bind is actually nameless.
    pub name: Symbol,
    /// The index in the sequence of target patterns, of this spread pattern.
    pub index: usize,
    /// The stack member that this spread pattern binds to, if any.
    pub stack_member: Option<StackMemberId>,
}

/// A range pattern containing two bounds `start` and `end`.
///
/// The `start` and `end` values must be either both [`LitPat::Int`], or both
/// [`LitPat::Char`].
#[derive(Copy, Clone, Debug)]
pub struct RangePat {
    /// The beginning of the range.
    pub start: LitPat,
    /// The end of the range.
    pub end: LitPat,
    /// If the range includes the `end` or not.
    pub range_end: RangeEnd,
}

/// Represents a pattern.
///
/// Check the documentation of each member for more information.
#[derive(Copy, Clone, Debug, From)]
pub enum Pat {
    Binding(BindingPat),
    Range(RangePat),
    Lit(LitPat),
    Tuple(TuplePat),
    Array(ArrayPat),
    Ctor(CtorPat),
    Or(OrPat),
    If(IfPat),
}

impl Pat {
    /// Check if the pattern is a [`Pat::Or`].
    pub fn is_or(&self) -> bool {
        matches!(self, Pat::Or(_))
    }

    /// Check if the pattern is of the [`Pat::Binding`] variant.
    pub fn is_bind(&self) -> bool {
        matches!(self, Pat::Binding(_))
    }

    /// Check if the pattern is wrapped with an `if` guard.
    pub fn is_if(&self) -> bool {
        matches!(self, Pat::If(_))
    }

    /// Convert the pattern into a binding pattern, if it is one.
    pub fn into_bind(self) -> Option<BindingPat> {
        match self {
            Pat::Binding(pat) => Some(pat),
            _ => None,
        }
    }
}

new_store_key!(pub PatId);
new_store!(pub PatStore<PatId, Pat>);

new_sequence_store_key!(pub PatListId);
pub type PatListStore = DefaultSequenceStore<PatListId, PatOrCapture>;

impl fmt::Display for WithEnv<'_, Spread> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let symbol_data = self.stores().symbol().get(self.value.name);
        if let Some(name) = symbol_data.name {
            write!(f, "...{name}")
        } else {
            write!(f, "...")
        }
    }
}

impl fmt::Display for WithEnv<'_, &RangePat> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.env().with(&self.value.start))?;
        match self.value.range_end {
            RangeEnd::Included => write!(f, "..=")?,
            RangeEnd::Excluded => write!(f, "..")?,
        }
        write!(f, "{}", self.env().with(&self.value.end))
    }
}

impl fmt::Display for WithEnv<'_, &Pat> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            Pat::Binding(binding_pat) => write!(f, "{}", self.env().with(binding_pat)),
            Pat::Range(range_pat) => write!(f, "{}", self.env().with(range_pat)),
            Pat::Lit(lit_pat) => write!(f, "{}", self.env().with(lit_pat)),
            Pat::Tuple(tuple_pat) => write!(f, "{}", self.env().with(tuple_pat)),
            Pat::Ctor(ctor_pat) => write!(f, "{}", self.env().with(ctor_pat)),
            Pat::Or(or_pat) => write!(f, "{}", self.env().with(or_pat)),
            Pat::If(if_pat) => write!(f, "{}", self.env().with(if_pat)),
            Pat::Array(list_pat) => write!(f, "{}", self.env().with(list_pat)),
        }
    }
}

impl fmt::Display for WithEnv<'_, PatId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().pat().map_fast(self.value, |pat| write!(f, "{}", self.env().with(pat)))
    }
}

impl fmt::Display for WithEnv<'_, (PatArgsId, Option<Spread>)> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().pat_args().map_fast(self.value.0, |pat_args| {
            let mut pat_args_formatted =
                pat_args.iter().map(|arg| self.env().with(arg).to_string()).collect::<Vec<_>>();

            if let Some(spread) = self.value.1 {
                pat_args_formatted.insert(spread.index, self.env().with(spread).to_string());
            }

            for (i, pat_arg) in pat_args_formatted.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{pat_arg}")?;
            }
            Ok(())
        })
    }
}
