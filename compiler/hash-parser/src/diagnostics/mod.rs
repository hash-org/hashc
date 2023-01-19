//! Hash Parser diagnostic utilities, error and warning definitions.
//! This module contains all of the logic that provides diagnostic
//! capabilities within the parser.
pub(crate) mod error;
pub(crate) mod warning;

use hash_reporting::{
    diagnostic::{AccessToDiagnosticsMut, DiagnosticsMut, MutableDiagnostics},
    reporter::Reports,
};

use self::{
    error::ParseError,
    warning::{ParseWarning, ParseWarningWrapper},
};
use crate::parser::AstGen;

impl<'stream, 'resolver> AstGen<'stream, 'resolver> {
    pub(super) fn into_reports(mut self) -> Reports {
        let current_source_id = self.resolver.current_source_id();
        self.diagnostics().into_reports(Reports::from, |warn| {
            Reports::from(ParseWarningWrapper(warn, current_source_id))
        })
    }
}

impl<'stream, 'resolver> AccessToDiagnosticsMut for AstGen<'stream, 'resolver> {
    type Error = ParseError;
    type Warning = ParseWarning;
    type Diagnostics = MutableDiagnostics<ParseError, ParseWarning>;

    fn diagnostics(&mut self) -> &mut Self::Diagnostics {
        &mut self.diagnostics
    }
}
