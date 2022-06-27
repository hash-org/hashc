//! Contains structures to keep track of terms and information relevant to them.
use std::cell::Cell;

use super::primitives::{ResolutionId, Term, TermId};
use slotmap::SlotMap;

/// Stores all the terms within a typechecking cycle.
///
/// terms are accessed by an ID, of type [TermId].
#[derive(Debug, Default)]
pub struct TermStore {
    data: SlotMap<TermId, Term>,
    /// Keeps track of the last ID used for unresolved terms.
    /// This will be incremented every time a [Term::Unresolved] is created.
    ///
    /// @@Future: In the future, resolution IDs can be used to implement a
    /// pointer-based unknown term resolution, where substitutions
    /// correspond to mutating terms rather than creating whole new ones.
    /// This could greatly improve performance.
    last_resolution_id: Cell<usize>,
}

impl TermStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a term, returning its assigned [TermId].
    pub fn create(&mut self, term: Term) -> TermId {
        self.data.insert(term)
    }

    /// Get a term by [TermId].
    ///
    /// If the term is not found, this function will panic. However, this
    /// shouldn't happen because the only way to acquire a term is to use
    /// [Self::create], and terms cannot be deleted.
    pub fn get(&self, term_id: TermId) -> &Term {
        self.data.get(term_id).unwrap()
    }

    /// Get a term by [TermId], mutably.
    ///
    /// If the term is not found, this function will panic.
    pub fn get_mut(&mut self, term_id: TermId) -> &mut Term {
        self.data.get_mut(term_id).unwrap()
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
