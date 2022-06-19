//! Contains operations to get the type of a term.
use crate::{
    error::TcResult,
    storage::{primitives::TermId, AccessToStorage, AccessToStorageMut, StorageRefMut},
};

/// Can resolve the type of a given term, as another term.
pub struct Typer<'gs, 'ls, 'cd> {
    storage: StorageRefMut<'gs, 'ls, 'cd>,
}

impl<'gs, 'ls, 'cd> AccessToStorage for Typer<'gs, 'ls, 'cd> {
    fn storages(&self) -> crate::storage::StorageRef {
        self.storage.storages()
    }
}

impl<'gs, 'ls, 'cd> AccessToStorageMut for Typer<'gs, 'ls, 'cd> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd> Typer<'gs, 'ls, 'cd> {
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd>) -> Self {
        Self { storage }
    }

    /// Get the type of the given term, as another term.
    pub fn ty_of_term(&mut self, _term_id: TermId) -> TcResult<TermId> {
        todo!()
    }
}
