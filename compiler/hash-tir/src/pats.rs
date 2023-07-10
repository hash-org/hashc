//! Definitions related to patterns.

use core::fmt;
use std::fmt::Debug;

use derive_more::From;
use hash_ast::ast::RangeEnd;
use hash_utils::store::{SequenceStore, Store, TrivialSequenceStoreKey};

use super::{
    args::{PatArgsId, PatOrCapture},
    control::{IfPat, OrPat},
    data::CtorPat,
    lits::LitPat,
    scopes::BindingPat,
    symbols::Symbol,
    tuples::TuplePat,
};
use crate::{
    arrays::ArrayPat, tir_debug_value_of_single_store_id, tir_get, tir_sequence_store_indirect,
    tir_single_store,
};

/// A spread "pattern" (not part of [`Pat`]), which can appear in list patterns,
/// tuple patterns, and constructor patterns.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Spread {
    /// The name of the spread bind.
    /// If `name` does not map to a specific `Identifier` name, it means
    /// that the bind is actually nameless.
    pub name: Symbol,
    /// The index in the sequence of target patterns, of this spread pattern.
    pub index: usize,
}

/// A range pattern containing two bounds `lo` and `hi`.
///
/// The `lo` and `hi` values must be either both [`LitPat::Int`], or both
/// [`LitPat::Char`].
#[derive(Copy, Clone, Debug)]
pub struct RangePat {
    /// The beginning of the range.
    pub lo: LitPat,

    /// The end of the range.
    pub hi: LitPat,

    /// If the range includes the `end` or not.
    pub end: RangeEnd,
}

/// Represents a pattern.
///
/// Check the documentation of each member for more information.
#[derive(Copy, Clone, Debug, From)]
pub enum Pat {
    /// A binding pattern, which assigns a name, and optionally specifies if
    /// the binding is mutable or not.
    Binding(BindingPat),

    /// A range pattern, which specifies a numerical range which will match
    /// between two numerical values, with an option to specify if the range
    /// is inclusive or not.
    Range(RangePat),

    /// A literal pattern, character, string, number, etc.
    Lit(LitPat),

    /// A tuple collection of patterns, e.g. `('A', 2)`, with an option to add a
    /// spread pattern.
    Tuple(TuplePat),

    /// An array pattern, with an option to specify a spread pattern.
    Array(ArrayPat),

    /// A constructor pattern, either being a struct or an enum variant, e.g.
    /// `Some(3)`.
    Ctor(CtorPat),

    /// A choice pattern, specifying a number of children patterns which are all
    /// matchable.
    Or(OrPat),

    /// A guarded pattern with a specified condition.
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

tir_single_store!(
    store = pub PatStore,
    id = pub PatId,
    value = Pat,
    store_name = pat
);

tir_debug_value_of_single_store_id!(PatId);

tir_sequence_store_indirect!(
    store = pub PatListStore,
    id = pub PatListId[PatOrCapture],
    store_name = pat_list
);

impl fmt::Display for Spread {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = tir_get!(self.name, name) {
            write!(f, "...{name}")
        } else {
            write!(f, "...")
        }
    }
}

impl fmt::Display for RangePat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.lo)?;
        match self.end {
            RangeEnd::Included => write!(f, "..=")?,
            RangeEnd::Excluded => write!(f, "..")?,
        }
        write!(f, "{}", self.hi)
    }
}

impl fmt::Display for Pat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pat::Binding(binding_pat) => write!(f, "{}", binding_pat),
            Pat::Range(range_pat) => write!(f, "{}", range_pat),
            Pat::Lit(lit_pat) => write!(f, "{}", lit_pat),
            Pat::Tuple(tuple_pat) => write!(f, "{}", tuple_pat),
            Pat::Ctor(ctor_pat) => write!(f, "{}", ctor_pat),
            Pat::Or(or_pat) => write!(f, "{}", or_pat),
            Pat::If(if_pat) => write!(f, "{}", if_pat),
            Pat::Array(list_pat) => write!(f, "{}", list_pat),
        }
    }
}

impl fmt::Display for PatId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

#[derive(Clone, Debug, From)]
pub struct PatArgsWithSpread {
    pub pat_args: PatArgsId,
    pub spread: Option<Spread>,
}

impl fmt::Display for PatArgsWithSpread {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut pat_args_formatted =
            self.pat_args.iter().map(|arg| (arg).to_string()).collect::<Vec<_>>();

        if let Some(spread) = self.spread {
            pat_args_formatted.insert(spread.index, spread.to_string());
        }

        for (i, pat_arg) in pat_args_formatted.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{pat_arg}")?;
        }
        Ok(())
    }
}
