//! Hash Parser diagnostic utilities, error and warning definitions.
//! This module contains all of the logic that provides diagnostic
//! capabilities within the parser.
pub(crate) mod error;
pub(crate) mod expected;
pub(crate) mod warning;

use hash_reporting::{
    diagnostic::{AccessToDiagnosticsMut, DiagnosticStore, DiagnosticsMut},
    reporter::Reports,
};

use self::{error::ParseError, warning::ParseWarning};
use crate::parser::AstGen;

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    pub(super) fn into_reports(mut self) -> Reports {
        self.diagnostics().into_reports(Reports::from, Reports::from)
    }
}

impl<'stream, 'resolver> AccessToDiagnosticsMut for AstGen<'stream, 'resolver> {
    type Diagnostics = DiagnosticStore<ParseError, ParseWarning>;

    fn diagnostics(&mut self) -> &mut Self::Diagnostics {
        &mut self.diagnostics
    }
}
