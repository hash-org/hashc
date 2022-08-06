//! Contains structures to keep track of terms and information relevant to them.
use std::cell::Cell;

use super::primitives::{ResolutionId, Term};
use hash_utils::{
    new_store_key,
    store::{DefaultStore, Store},
};

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
