//! Hash Parser diagnostic utilities, error and warning definitions.
//! This module contains all of the logic that provides diagnostic
//! capabilities within the parser.
pub(crate) mod error;
pub(crate) mod expected;
pub(crate) mod warning;

use hash_reporting::diagnostic::{DiagnosticCellStore, Diagnostics, HasDiagnostics};

use self::{error::ParseError, warning::ParseWarning};
use crate::parser::AstGen;

/// Shorthand for the parser diagnostics.
pub type ParserDiagnostics = DiagnosticCellStore<ParseError, ParseWarning>;

impl<'s> HasDiagnostics for AstGen<'s> {
    type Diagnostics = ParserDiagnostics;

    fn diagnostics(&self) -> &Self::Diagnostics {
        self.diagnostics
    }

    fn add_error(
        &self,
        error: <Self::Diagnostics as hash_reporting::diagnostic::Diagnostics>::Error,
    ) {
        self.frame.errors.set(true);
        self.diagnostics().add_error(error);
    }

    fn maybe_add_error<T>(&mut self, value: Result<T, <Self::Diagnostics as Diagnostics>::Error>) {
        if let Err(value) = value {
            self.add_error(value);
        }
    }
}
