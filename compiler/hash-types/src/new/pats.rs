//! Definitions related to patterns.

use hash_ast::ast::RangeEnd;
use hash_utils::{new_sequence_store_key, new_store, new_store_key, store::DefaultSequenceStore};

use super::{
    control::{IfPat, OrPat},
    data::CtorPat,
    lits::LitPat,
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

/// A list pattern.
///
/// This is in the form `[x_1,...,x_n]`, with an optional spread `...(name?)` at
/// some position.
#[derive(Copy, Clone, Debug)]
pub struct ListPat {
    /// The sequence of patterns in the list pattern.
    pub pats: PatListId,
    /// The spread pattern, if any.
    pub spread: Option<Spread>,
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
    Ctor(CtorPat),
    List(ListPat),
    Or(OrPat),
    If(IfPat),
}

new_store_key!(pub PatId);
new_store!(pub PatStore<PatId, Pat>);

new_sequence_store_key!(pub PatListId);
pub type PatListStore = DefaultSequenceStore<PatListId, PatId>;
