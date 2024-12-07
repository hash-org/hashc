//! Hash Parser diagnostic utilities, error and warning definitions.
//! This module contains all of the logic that provides diagnostic
//! capabilities within the parser.
pub(crate) mod error;
pub(crate) mod expected;
pub(crate) mod warning;

use hash_reporting::diagnostic::{DiagnosticStore, DiagnosticsMut, HasDiagnosticsMut};

use self::{error::ParseError, warning::ParseWarning};
use crate::parser::AstGen;

/// Shorthand for the parser diagnostics.
pub type ParserDiagnostics = DiagnosticStore<ParseError, ParseWarning>;

impl HasDiagnosticsMut for AstGen<'_> {
    type Diagnostics = ParserDiagnostics;

    fn diagnostics(&mut self) -> &mut Self::Diagnostics {
        self.diagnostics
    }

    fn add_error(&mut self, error: <Self::Diagnostics as DiagnosticsMut>::Error) {
        // Specify that an error occurred in the current frame, so that the
        // frame exit handler can avoid emitting an `expected_eof`.
        self.frame.error.set(true);
        self.diagnostics().add_error(error);
    }
}
