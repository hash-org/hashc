//! Typechecking cache manager

use hash_utils::store::PartialStore;

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
pub struct CacheManager<'tc> {
    storage: StorageRefMut<'tc>,
}

impl<'tc> AccessToStorage for CacheManager<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> AccessToStorageMut for CacheManager<'tc> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'tc> CacheManager<'tc> {
    /// Create a new [CacheManager].
    pub fn new(storage: StorageRefMut<'tc>) -> Self {
        Self { storage }
    }

    /// Check whether `simplification` has been performed on the
    /// given [TermId].
    pub(crate) fn has_been_simplified(&self, term: TermId) -> Option<TermId> {
        self.cache().simplification_store.get(term)
    }

    /// Check whether a `validation` has been performed on the given
    /// [TermId].
    pub(crate) fn has_been_validated(&self, term: TermId) -> Option<TermValidation> {
        self.cache().validation_store.get(term)
    }

    /// Check whether a `unification` has been performed on the given
    /// [TermId].
    pub(crate) fn has_been_unified(&self, pair: (TermId, TermId)) -> Option<Sub> {
        self.cache().unification_store.get(pair)
    }

    /// Check whether a `validation` has been performed on the given
    /// [TermId].
    pub(crate) fn has_been_inferred(&self, term: TermId) -> Option<TermId> {
        self.cache().inference_store.get(term)
    }

    /// Record an entry for a `simplification` operation.
    pub(crate) fn add_simplification_entry(&self, key: TermId, value: TermId) {
        self.cache().simplification_store.insert(key, value);
    }

    /// Record an entry for a `validation` operation.
    pub(crate) fn add_validation_entry(&self, key: TermId, value: TermValidation) {
        self.cache().validation_store.insert(key, value);
    }

    /// Record an entry for a `unification` operation.
    pub(crate) fn add_unification_entry(&self, key: (TermId, TermId), value: &Sub) {
        self.cache().unification_store.insert(key, value.clone());
    }

    /// Record an entry for a `inference` operation.
    pub(crate) fn add_inference_entry(&self, key: TermId, value: TermId) {
        self.cache().inference_store.insert(key, value);
    }
}
