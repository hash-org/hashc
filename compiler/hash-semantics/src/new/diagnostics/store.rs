use std::cell::RefCell;

use super::{error::TcError, warning::TcWarning};

#[derive(Debug, Default)]
pub struct DiagnosticsStore {
    errors: RefCell<Vec<TcError>>,
    warnings: RefCell<Vec<TcWarning>>,
}

impl DiagnosticsStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn errors_owned(&self) -> Vec<TcError> {
        self.errors.borrow().clone()
    }

    pub fn warnings_owned(&self) -> Vec<TcWarning> {
        self.warnings.borrow().clone()
    }

    pub fn add_error(&self, error: TcError) {
        self.errors.borrow_mut().push(error);
    }

    pub fn add_warning(&self, warning: TcWarning) {
        self.warnings.borrow_mut().push(warning);
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.borrow().is_empty()
    }

    pub fn has_warnings(&self) -> bool {
        !self.warnings.borrow().is_empty()
    }

    pub fn clear(&self) {
        self.errors.borrow_mut().clear();
        self.warnings.borrow_mut().clear();
    }
}
