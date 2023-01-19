//! Definitions related to patterns.

use core::fmt;

use hash_ast::ast::RangeEnd;
use hash_utils::{
    new_sequence_store_key, new_store, new_store_key,
    store::{CloneStore, DefaultSequenceStore, Store},
};

use super::{
    control::{IfPat, OrPat},
    data::CtorPat,
    environment::env::{AccessToEnv, WithEnv},
    lits::{ListPat, LitPat},
    scopes::BindingPat,
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
#[derive(Copy, Clone, Debug)]
pub enum Pat {
    Binding(BindingPat),
    Range(RangePat),
    Lit(LitPat),
    Tuple(TuplePat),
    List(ListPat),
    Ctor(CtorPat),
    Or(OrPat),
    If(IfPat),
}

new_store_key!(pub PatId);
new_store!(pub PatStore<PatId, Pat>);

new_sequence_store_key!(pub PatListId);
pub type PatListStore = DefaultSequenceStore<PatListId, PatId>;

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
            Pat::List(list_pat) => write!(f, "{}", self.env().with(list_pat)),
        }
    }
}

impl fmt::Display for WithEnv<'_, PatId> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.stores().pat().map_fast(self.value, |pat| write!(f, "{}", self.env().with(pat)))
    }
}