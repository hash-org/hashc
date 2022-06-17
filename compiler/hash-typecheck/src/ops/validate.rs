//! Contains utilities to validate terms.
use crate::{
    error::TcResult,
    storage::{primitives::TermId, AccessToStorage, AccessToStorageMut, StorageRefMut},
};

/// Can resolve the type of a given term, as another term.
pub struct Validator<'gs, 'ls, 'cd> {
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for Validator<'gs, 'ls, 'cd> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> AccessToStorageMut for Validator<'gs, 'ls, 'cd> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd> Validator<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    /// Validate the given term for correctness.
    pub fn validate_term(&mut self, _term_id: TermId) -> TcResult<()> {
        todo!()
    }
}
