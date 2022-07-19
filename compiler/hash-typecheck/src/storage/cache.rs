//! Typechecking operations cache storing results for previous simplifications,
//! unifications, and validations.

use std::collections::HashMap;

use crate::ops::validate::TermValidation;

use super::primitives::{Sub, TermId};

/// The typechecking cache.
///
/// The cache has no bound, and no eviction policy.
#[derive(Debug, Default)]
pub struct Cache {
    /// Inner store for the results from term simplifications.
    pub(crate) simplification_store: HashMap<TermId, TermId>,
    /// Inner store for the results from term simplifications.
    pub(crate) validation_store: HashMap<TermId, TermValidation>,
    /// Inner store for the results from term unifications.
    pub(crate) unification_store: HashMap<(TermId, TermId), Sub>,
    /// Number of times the cache successfully retrieved a result
    pub(crate) hits: usize,
    /// Number of times the cache didn't have an operation stored
    pub(crate) misses: usize,
}

impl Cache {
    /// Create a new [Cache]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new [Cache] with an initial capacity. The capacity
    /// value is used for each inner operation store.
    pub fn new_with_capacity(capacity: usize) -> Self {
        Self {
            simplification_store: HashMap::with_capacity(capacity),
            validation_store: HashMap::with_capacity(capacity),
            unification_store: HashMap::with_capacity(capacity),
            hits: 0,
            misses: 0,
        }
    }

    fn record<V: Copy>(&mut self, value: Option<V>) -> Option<V> {
        match value {
            Some(value) => {
                self.hits += 1;
                Some(value)
            }
            None => {
                self.misses += 1;
                None
            }
        }
    }

    /// Check whether a `simplification` has been performed on the given
    /// [Term].
    pub(crate) fn has_been_simplified(&mut self, term: TermId) -> Option<TermId> {
        let term = self.simplification_store.get(&term).copied();
        self.record(term)
    }

    /// Check whether a `validation` has been performed on the given
    /// [Term].
    pub(crate) fn has_been_validated(&mut self, term: TermId) -> Option<TermValidation> {
        let term = self.validation_store.get(&term).copied();
        self.record(term)
    }

    /// Check whether a `validation` has been performed on the given
    /// [Term].
    pub(crate) fn has_been_unified(&mut self, pair: (TermId, TermId)) -> Option<Sub> {
        let sub = self.unification_store.get(&pair).cloned();

        match sub {
            Some(value) => {
                self.hits += 1;
                Some(value)
            }
            None => {
                self.misses += 1;
                None
            }
        }
    }

    /// Record an entry for a simplification operation.
    pub(crate) fn add_simplification_entry(&mut self, key: TermId, value: TermId) {
        self.simplification_store.insert(key, value);
    }

    /// Record an entry for a simplification operation.
    pub(crate) fn add_validation_entry(&mut self, key: TermId, value: TermValidation) {
        self.validation_store.insert(key, value);
    }

    pub(crate) fn add_unification_entry(&mut self, key: (TermId, TermId), value: &Sub) {
        self.unification_store.insert(key, value.clone());
    }
}
