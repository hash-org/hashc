//! Module file for diagnostic creation and reporting within the typechecking
//! crate.
pub mod error;
pub mod params;
pub mod reporting;
pub mod warning;

pub(crate) mod macros;

use std::cell::RefCell;

use hash_reporting::diagnostic::Diagnostics;
use smallvec::SmallVec;

use self::{
    error::TcError,
    reporting::TcErrorWithStorage,
    warning::{TcWarning, TcWarningWithStorage},
};
use crate::storage::AccessToStorage;

/// [TcDiagnostics] is a struct that stores the generated errors
/// and warnings for the typechecking instance.
#[derive(Debug, Default)]
pub struct TcDiagnostics {
    /// The errors that the typechecking instance has emitted.
    pub(super) errors: RefCell<SmallVec<[TcError; 1]>>,
    /// The warnings that the typechecking instance has emitted.
    pub(super) warnings: RefCell<Vec<TcWarning>>,
}

pub struct TcDiagnosticsWrapper<'tc, T: ?Sized>(pub(crate) &'tc T);

impl<'tc, T: AccessToStorage> Diagnostics<TcError, TcWarning> for TcDiagnosticsWrapper<'tc, T> {
    type DiagnosticsStore = TcDiagnostics;

    fn diagnostic_store(&self) -> &'tc Self::DiagnosticsStore {
        self.0.diagnostic_store()
    }

    /// Implementing this access method is not possible for the typechecking
    /// context and in fact is un-necessary
    fn diagnostic_store_mut(&mut self) -> &mut Self::DiagnosticsStore {
        unimplemented!()
    }

    fn add_error(&mut self, error: TcError) {
        self.diagnostic_store().errors.borrow_mut().push(error);
    }

    fn add_warning(&mut self, warning: TcWarning) {
        self.diagnostic_store().warnings.borrow_mut().push(warning);
    }

    fn has_errors(&self) -> bool {
        !self.diagnostic_store().errors.borrow().is_empty()
    }

    fn has_warnings(&self) -> bool {
        !self.diagnostic_store().warnings.borrow().is_empty()
    }

    fn into_reports(self) -> Vec<hash_reporting::report::Report> {
        let TcDiagnostics { errors, warnings } = self.diagnostic_store();

        let errors = errors.clone().into_inner();
        let warnings = warnings.clone().into_inner();

        errors
            .into_iter()
            .map(|error| TcErrorWithStorage { error, storage: self.0.storages() }.into())
            .chain(
                warnings.into_iter().map(|warning| {
                    TcWarningWithStorage { warning, storage: self.0.storages() }.into()
                }),
            )
            .collect()
    }

    fn into_diagnostics(self) -> (Vec<TcError>, Vec<TcWarning>) {
        let diagnostics = self.diagnostic_store();

        (
            diagnostics.errors.clone().into_inner().to_vec(),
            diagnostics.warnings.clone().into_inner(),
        )
    }

    fn merge_diagnostics(&mut self, other: impl Diagnostics<TcError, TcWarning>) {
        let (errors, warnings) = other.into_diagnostics();

        self.diagnostic_store().errors.borrow_mut().extend(errors);
        self.diagnostic_store().warnings.borrow_mut().extend(warnings);
    }
}
