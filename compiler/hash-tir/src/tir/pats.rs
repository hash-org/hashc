//! Definitions related to patterns.

use core::fmt;
use std::fmt::Debug;

use hash_ast::ast::RangeEnd;
use hash_storage::{
    get,
    store::{statics::StoreId, TrivialSequenceStoreKey},
};
use hash_utils::derive_more::From;

use super::TermId;
use crate::{
    scopes::BindingPat,
    stores::tir_stores,
    tir::{
        ArrayPat, CtorPat, CtorTerm, IfPat, LitPat, NodeId, OrPat, PatArgsId, PatOrCapture,
        SymbolId, Term, TuplePat, TupleTerm,
    },
    tir_node_sequence_store_indirect, tir_node_single_store,
};

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

    /// A literal pattern, `3`, `'a'`, or `"мир"`.
    Lit(LitPat),

    /// A tuple collection of patterns, e.g. `('A', 2)`, `(1, 2, ...)`.
    Tuple(TuplePat),

    /// An array pattern, e.g. `[1, 2, 3]`, [1, ...]`.
    Array(ArrayPat),

    /// A constructor pattern, `Some(3)`, `X(name = "y", age = 12)`.
    Ctor(CtorPat),

    /// A choice pattern, `a | b | c`.
    Or(OrPat),

    /// A guarded pattern with a specified condition, `a if a > 0`.
    If(IfPat),
}

tir_node_single_store!(Pat);
tir_node_sequence_store_indirect!(PatList[PatOrCapture]);

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

impl PatId {
    /// Try to use the pattern as a term.
    ///
    /// This is only possible for patterns that are not [`Pat::Or`].
    pub fn try_use_as_term(&self) -> Option<TermId> {
        let origin = self.origin();
        match *self.value() {
            Pat::Binding(var) => Some(Term::from(var.name, origin)),
            Pat::Range(_) => Some(Term::from(SymbolId::fresh(origin), origin)),
            Pat::Lit(lit) => Some(Term::from(Term::Lit(*lit), origin)),
            Pat::Ctor(ctor_pat) => Some(Term::from(
                CtorTerm {
                    ctor: ctor_pat.ctor,
                    data_args: ctor_pat.data_args,
                    ctor_args: ctor_pat.ctor_pat_args.try_use_as_term_args()?,
                },
                origin,
            )),
            Pat::Tuple(tuple_pat) => {
                Some(Term::from(TupleTerm { data: tuple_pat.data.try_use_as_term_args()? }, origin))
            }
            Pat::Array(_) => None, // @@Improvement: we can use this as a term too
            Pat::Or(_) => None,
            Pat::If(if_pat) => if_pat.pat.try_use_as_term(),
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
        write!(f, "{}", *self.value())
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
