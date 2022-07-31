//! Typechecking cache manager

use crate::storage::{
    primitives::{Sub, TermId},
    AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
};

use super::validate::TermValidation;

/// The typechecking cache manager. Allows for recording results from
/// simplification, unification, validation, and inference operations.
///
/// Whilst the [CacheManager] manages the internal
/// [Cache](crate::storage::cache::Cache), the manager itself does not contain
/// any logic that governs how the cache evicts its entries.
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
    /// Create a new [CacheManager].
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    /// Check whether `simplification` has been performed on the
    /// given [TermId].
    pub(crate) fn has_been_simplified(&mut self, term: TermId) -> Option<TermId> {
        self.cache_mut().simplification_store.get(term).copied()
    }

    /// Check whether a `validation` has been performed on the given
    /// [TermId].
    pub(crate) fn has_been_validated(&mut self, term: TermId) -> Option<TermValidation> {
        self.cache_mut().validation_store.get(term).copied()
    }

    /// Check whether a `unification` has been performed on the given
    /// [TermId].
    pub(crate) fn has_been_unified(&mut self, pair: (TermId, TermId)) -> Option<Sub> {
        self.cache_mut().unification_store.get(pair).cloned()
    }

    /// Check whether a `validation` has been performed on the given
    /// [TermId].
    pub(crate) fn has_been_inferred(&mut self, term: TermId) -> Option<TermId> {
        self.cache_mut().inference_store.get(term).copied()
    }

    /// Record an entry for a `simplification` operation.
    pub(crate) fn add_simplification_entry(&mut self, key: TermId, value: TermId) {
        self.cache_mut().simplification_store.put(key, value);
    }

    /// Record an entry for a `validation` operation.
    pub(crate) fn add_validation_entry(&mut self, key: TermId, value: TermValidation) {
        self.cache_mut().validation_store.put(key, value);
    }

    /// Record an entry for a `unification` operation.
    pub(crate) fn add_unification_entry(&mut self, key: (TermId, TermId), value: &Sub) {
        self.cache_mut().unification_store.put(key, value.clone());
    }

    /// Record an entry for a `inference` operation.
    pub(crate) fn add_inference_entry(&mut self, key: TermId, value: TermId) {
        self.cache_mut().inference_store.put(key, value);
    }
}
