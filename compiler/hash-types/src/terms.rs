//! Contains structures to keep track of terms and information relevant to them.
use std::{cell::Cell, fmt::Display};

use hash_utils::{
    new_sequence_store_key, new_store_key,
    store::{DefaultSequenceStore, DefaultStore, Store},
};

use crate::{ResolutionId, Term};

new_store_key!(pub TermId);

/// Stores all the terms within a typechecking cycle.
///
/// terms are accessed by an ID, of type [TermId].
#[derive(Debug, Default)]
pub struct TermStore {
    data: DefaultStore<TermId, Term>,
    /// Keeps track of the last ID used for unresolved terms.
    /// This will be incremented every time a [Term::Unresolved] is created.
    ///
    /// @@Future: In the future, resolution IDs can be used to implement a
    /// pointer-based unknown term resolution, where substitutions
    /// correspond to mutating terms rather than creating whole new ones.
    /// This could greatly improve performance.
    last_resolution_id: Cell<usize>,
}

impl Store<TermId, Term> for TermStore {
    fn internal_data(&self) -> &std::cell::RefCell<Vec<Term>> {
        self.data.internal_data()
    }
}

impl TermStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Get a new [ResolutionId] for a new [Term::Unresolved].
    ///
    /// This shouldn't be directly used in inference code, rather call the
    /// appropriate
    /// [PrimitiveBuilder](crate::ops::building::PrimitiveBuilder) function.
    pub fn new_resolution_id(&self) -> ResolutionId {
        let new_id = self.last_resolution_id.get() + 1;
        self.last_resolution_id.set(new_id);
        ResolutionId(new_id)
    }
}

new_sequence_store_key!(pub TermListId);

/// Define the [TermListStore], which is a sequence of [Term]s associated
/// with a [TermListId].
pub type TermListStore = DefaultSequenceStore<TermListId, TermId>;

/// Represents the level of a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// A enumeration of the level kinds that terms can be.
pub enum TermLevel {
    /// Couldn't be determined and thus labelled as unknown
    Unknown,
    /// Level 0 terms
    Level0,
    /// Level 1 terms
    Level1,
    /// Level 2 terms
    Level2,
    /// Level 3 terms
    Level3,
    /// Level 4 terms, specifically [Term::Root]
    Level4,
}

impl Display for TermLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TermLevel::Unknown => write!(f, "unknown"),
            TermLevel::Level0 => write!(f, "level-0"),
            TermLevel::Level1 => write!(f, "level-1"),
            TermLevel::Level2 => write!(f, "level-2"),
            TermLevel::Level3 => write!(f, "level-3"),
            TermLevel::Level4 => write!(f, "level-4"),
        }
    }
}

impl Term {
    /// Compute the level of the term. This is a primitive computation
    /// and does not attempt to compute the true level of the [Term]
    /// by looking at the inner children of the [Term].
    pub fn get_term_level(&self, _store: &TermStore) -> TermLevel {
        // @@Todo(feds01): implement the other variants by recursing into them.
        // This should be done on a struct with access to storage
        match self {
            Term::Access(_)
            | Term::Var(_)
            | Term::Merge(_)
            | Term::TyFn(_)
            | Term::TyOf(_)
            | Term::Union(_)
            | Term::SetBound(_)
            | Term::ScopeVar(_)
            | Term::BoundVar(_)
            | Term::TyFnTy(_)
            | Term::TyFnCall(_) => TermLevel::Unknown,
            Term::Unresolved(_) => TermLevel::Unknown,
            Term::Root => TermLevel::Level4,
            Term::Level3(_) => TermLevel::Level3,
            Term::Level2(_) => TermLevel::Level2,
            Term::Level1(_) => TermLevel::Level1,
            Term::Level0(_) => TermLevel::Level0,
        }
    }
}
