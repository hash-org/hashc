//! Functionality related to determining properties about terms and other
//! constructs.
use crate::storage::{
    primitives::{IntKind, TermId},
    AccessToStorage, AccessToStorageMut, StorageRef, StorageRefMut,
};

use super::AccessToOpsMut;

pub struct Oracle<'tc> {
    storage: StorageRefMut<'tc>,
}

impl<'tc> AccessToStorage for Oracle<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}
impl<'tc> AccessToStorageMut for Oracle<'tc> {
    fn storages_mut(&mut self) -> StorageRefMut {
        self.storage.storages_mut()
    }
}

impl<'tc> Oracle<'tc> {
    pub fn new(storage: StorageRefMut<'tc>) -> Self {
        Self { storage }
    }

    /// If the term is a string type.
    pub fn term_is_str(&mut self, term: TermId) -> bool {
        let str_ty = self.core_defs().str_ty();
        self.unifier().terms_are_equal(term, str_ty)
    }

    /// If the term is a char type.
    pub fn term_is_char(&mut self, term: TermId) -> bool {
        let char_ty = self.core_defs().char_ty();
        self.unifier().terms_are_equal(term, char_ty)
    }

    /// If the term is an integer type, returns its [IntKind].
    pub fn term_as_int(&mut self, _term: TermId) -> Option<IntKind> {
        todo!()
    }

    /// If the term is a list type, returns its inner type.
    pub fn term_as_list(&mut self, _term: TermId) -> Option<TermId> {
        todo!()
    }

    /// If the term is the never type.
    pub fn term_is_never(&mut self, _term: TermId) -> bool {
        todo!()
    }
}
