//! Contains utilities to validate terms.
use crate::{
    error::TcResult,
    storage::{primitives::TermId, AccessToStorage, AccessToStorageMut, StorageRefMut},
};

/// Represents the level of a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TermLevel {
    Level0,
    Level1,
    Level2,
    Level3,
}

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

    /// Determine whether the given term is constant, i.e. has no side effects.
    ///
    /// This is the condition for the term to be able to be used as the return type of a type
    /// function, or to be used in global scope.
    pub fn term_is_constant(&mut self, _term_id: TermId) -> TcResult<bool> {
        todo!()
    }

    /// Determine the level of the given term.
    pub fn get_level_of_term(&mut self, _term_id: TermId) -> TcResult<TermLevel> {
        todo!()
    }
}
