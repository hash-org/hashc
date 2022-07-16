//! Functionality related to pattern matching.

use crate::{
    diagnostics::error::TcResult,
    storage::{
        primitives::{Member, PatternId, TermId},
        AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
    },
};

/// Contains functions related to pattern matching.
pub struct PatternMatcher<'gs, 'ls, 'cd, 's> {
    storage: StorageRefMut<'gs, 'ls, 'cd, 's>,
}

impl<'gs, 'ls, 'cd, 's> AccessToStorage for PatternMatcher<'gs, 'ls, 'cd, 's> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}
impl<'gs, 'ls, 'cd, 's> AccessToStorageMut for PatternMatcher<'gs, 'ls, 'cd, 's> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'gs, 'ls, 'cd, 's> PatternMatcher<'gs, 'ls, 'cd, 's> {
    /// Create a new [PatternMatcher].
    pub fn new(storage: StorageRefMut<'gs, 'ls, 'cd, 's>) -> Self {
        Self { storage }
    }

    /// Match the given pattern with the given term, returning
    /// `Some(member_list)` if the pattern matches (with a list of bound
    /// members), or `None` if it doesn't match. If the types mismatch, it
    /// returns an error.
    pub fn match_pattern_with_term(
        _pattern: PatternId,
        _term: TermId,
    ) -> TcResult<Option<Vec<Member>>> {
        todo!()
    }
}
