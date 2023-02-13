//! Typechecking cache manager

use hash_tir::old::terms::TermId;
use hash_utils::store::PartialStore;

use super::validate::TermValidation;
use crate::storage::{AccessToStorage, StorageRef};

/// The typechecking cache manager. Allows for recording results from
/// simplification, unification, validation, and inference operations.
///
/// Whilst the [CacheManager] manages the internal
/// [Cache](crate::storage::cache::Cache), the manager itself does not contain
/// any logic that governs how the cache evicts its entries.
pub struct CacheManager<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for CacheManager<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> CacheManager<'tc> {
    /// Create a new [CacheManager].
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// Check whether a `validation` has been performed on the given
    /// [TermId].
    pub(crate) fn has_been_validated(&self, term: TermId) -> Option<TermValidation> {
        self.cache().validation_store.get(term)
    }

    /// Check whether a `validation` has been performed on the given
    /// [TermId].
    pub(crate) fn has_been_inferred(&self, term: TermId) -> Option<TermId> {
        self.cache().inference_store.get(term)
    }

    /// Record an entry for a `validation` operation.
    pub(crate) fn add_validation_entry(&self, key: TermId, value: TermValidation) {
        self.cache().validation_store.insert(key, value);
    }

    /// Record an entry for a `inference` operation.
    pub(crate) fn add_inference_entry(&self, key: TermId, value: TermId) {
        self.cache().inference_store.insert(key, value);
    }
}
