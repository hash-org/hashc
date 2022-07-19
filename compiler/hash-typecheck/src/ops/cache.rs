//! Typechecking cache manager

use crate::storage::{
    primitives::{Sub, TermId},
    AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
};

use super::validate::TermValidation;

/// The typechecking cache.
///
/// The cache has no bound, and no eviction policy.
#[derive(Debug)]
pub struct CacheManager<'gs, 'ls, 'cd, 's> {
    storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for CacheManager<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}
impl<'gs, 'ls, 'cd, 's> AccessToStorageMut for CacheManager<'gs, 'ls, 'cd, 's> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 's> CacheManager<'gs, 'ls, 'cd, 's> {
    /// Create a new [PatternMatcher].
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    pub(crate) fn has_been_simplified(&mut self, term: TermId) -> Option<TermId> {
        self.cache_mut().simplification_store.get(term).copied()
    }

    /// Check whether a `validation` has been performed on the given
    /// [Term].
    pub(crate) fn has_been_validated(&mut self, term: TermId) -> Option<TermValidation> {
        self.cache_mut().validation_store.get(term).copied()
    }

    /// Check whether a `validation` has been performed on the given
    /// [Term].
    pub(crate) fn has_been_unified(&mut self, pair: (TermId, TermId)) -> Option<Sub> {
        self.cache_mut().unification_store.get(pair).cloned()
    }

    /// Record an entry for a simplification operation.
    pub(crate) fn add_simplification_entry(&mut self, key: TermId, value: TermId) {
        self.cache_mut().simplification_store.put(key, value);
    }

    /// Record an entry for a simplification operation.
    pub(crate) fn add_validation_entry(&mut self, key: TermId, value: TermValidation) {
        self.cache_mut().validation_store.put(key, value);
    }

    pub(crate) fn add_unification_entry(&mut self, key: (TermId, TermId), value: &Sub) {
        self.cache_mut().unification_store.put(key, value.clone());
    }
}
