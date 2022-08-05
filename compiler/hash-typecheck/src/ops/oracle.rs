//! Functionality related to determining properties about terms and other
//! constructs.
use hash_ast::ast::IntTy;

use crate::storage::{primitives::TermId, AccessToStorage, StorageRef};

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
    pub fn term_is_str(&mut self, _term: TermId) -> bool {
        todo!()
    }

    /// If the term is a char type.
    pub fn term_is_char(&mut self, _term: TermId) -> bool {
        todo!()
    }

    /// If the term is an integer type, returns its [IntTy].
    pub fn term_as_int(&mut self, _term: TermId) -> Option<IntTy> {
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
