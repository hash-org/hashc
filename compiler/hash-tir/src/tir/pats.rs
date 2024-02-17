//! Definitions related to patterns.

use core::fmt;
use std::fmt::Debug;

use hash_ast::ast::RangeEnd;
use hash_storage::{
    get,
    store::{statics::StoreId, TrivialSequenceStoreKey},
};
use hash_utils::derive_more::From;

use super::{NodeOrigin, TermId, TermListId};
use crate::{
    stores::tir_stores,
    tir::{ArrayPat, CtorTerm, IfPat, LitPat, NodeId, OrPat, PatArgsId, SymbolId, Term, TupleTerm},
    tir_node_sequence_store_indirect, tir_node_single_store,
};

/// A binding pattern, which is essentially a declaration left-hand side.
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub struct BindingPat {
    /// The name of the bind.
    /// If `name` does not map to a specific `Identifier` name, it means
    /// that the pattern is actually a wildcard `_`.
    pub name: SymbolId,
    /// Whether the binding is declared as mutable.
    pub is_mutable: bool,
}

impl fmt::Display for BindingPat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", if self.is_mutable { "mut " } else { "" }, self.name)
    }
}

/// A spread "pattern" (not part of [`Pat`]), which can appear in list patterns,
/// tuple patterns, and constructor patterns.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Spread {
    /// The name of the spread bind.
    /// If `name` does not map to a specific `Identifier` name, it means
    /// that the bind is actually nameless.
    pub name: SymbolId,
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
    pub lo: Option<LitPat>,

    /// The end of the range.
    pub hi: Option<LitPat>,

    /// If the range includes the `end` or not.
    pub end: RangeEnd,
}

/// Represents a pattern.
///
/// Check the documentation of each member for more information.
#[derive(Copy, Clone, Debug, From)]
pub enum Pat {
    /// A binding pattern, `mut k`, `k`, or `_`.
    Binding(BindingPat),

    /// A range pattern, `1..10` or `'a'..<'z'`.
    Range(RangePat),

    /// A spread pattern.
    Spread(Spread),

    /// A choice pattern, `a | b | c`.
    Or(OrPat),

    /// A guarded pattern with a specified condition, `a if a > 0`.
    If(IfPat),
}

pub type PatId = TermId;
pub type PatListId = TermListId;

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

    /// Try to use the pattern as a term.
    ///
    /// This is only possible for patterns that are not [`Pat::Or`].
    pub fn try_use_as_term(&self, origin: NodeOrigin) -> Option<TermId> {
        match self {
            Pat::Binding(var) => Some(Term::from(var.name, origin)),
            Pat::Range(_) => Some(Term::from(SymbolId::fresh(origin), origin)),
            Pat::Or(_) => None,
            Pat::If(if_pat) => Some(if_pat.pat),
            Pat::Spread(_) => None,
        }
    }
}

impl fmt::Display for Spread {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = get!(self.name, name) {
            write!(f, "...{name}")
        } else {
            write!(f, "...")
        }
    }
}

impl fmt::Display for RangePat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.lo.map_or(Ok(()), |lo| write!(f, "{}", lo))?;

        match self.end {
            RangeEnd::Included => write!(f, "..")?,
            RangeEnd::Excluded => write!(f, "..<")?,
        }

        self.hi.map_or(Ok(()), |hi| write!(f, "{}", hi))
    }
}

impl fmt::Display for Pat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pat::Binding(binding_pat) => write!(f, "{}", binding_pat),
            Pat::Range(range_pat) => write!(f, "{}", range_pat),
            Pat::Or(or_pat) => write!(f, "{}", or_pat),
            Pat::If(if_pat) => write!(f, "{}", if_pat),
            Pat::Spread(spread) => write!(f, "{}", spread),
        }
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
