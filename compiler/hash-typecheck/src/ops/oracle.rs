//! Functionality related to determining properties about terms and other
//! constructs.
use hash_ast::ast::IntTy;

use super::AccessToOps;
use crate::storage::{terms::TermId, AccessToStorage, StorageRef};

pub struct Oracle<'tc> {
    storage: StorageRef<'tc>,
}

impl<'tc> AccessToStorage for Oracle<'tc> {
    fn storages(&self) -> StorageRef {
        self.storage.storages()
    }
}

impl<'tc> Oracle<'tc> {
    pub fn new(storage: StorageRef<'tc>) -> Self {
        Self { storage }
    }

    /// If the term is a string type.
    pub fn term_is_str(&self, term: TermId) -> bool {
        self.unifier().terms_are_equal(term, self.core_defs().str_ty())
    }

    /// If the term is a char type.
    pub fn term_is_char(&self, term: TermId) -> bool {
        self.unifier().terms_are_equal(term, self.core_defs().char_ty())
    }

    /// If the term is an integer type, returns its [IntTy].
    pub fn term_as_int(&self, _term: TermId) -> Option<IntTy> {
        // @@Todo:
        None
    }

    /// If the term is a list type, returns its inner type.
    pub fn term_as_list(&self, _term: TermId) -> Option<TermId> {
        // @@Todo:
        None
    }

    /// If the term is the never type.
    pub fn term_is_never(&self, term: TermId) -> bool {
        self.unifier().terms_are_equal(term, self.builder().create_never_ty())
    }
}
