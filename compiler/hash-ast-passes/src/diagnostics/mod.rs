//! Hash AST semantic passes diagnostic definitions and logic.
#![allow(dead_code)]

use hash_reporting::{diagnostic::Diagnostics, report::Report};

use self::{error::AnalysisError, warning::AnalysisWarning};
use crate::analysis::SemanticAnalyser;

pub(crate) mod directives;
pub(crate) mod error;
pub(crate) mod origins;
pub(crate) mod warning;

/// Store [SemanticAnalyser] diagnostics which can be errors or warnings.
#[derive(Default)]
pub struct AnalyserDiagnostics {
    /// Any errors that the [SemanticAnalyser] produces.
    errors: Vec<AnalysisError>,
    /// Any warnings that the [SemanticAnalyser] produces.
    warnings: Vec<AnalysisWarning>,
}

impl Diagnostics<AnalysisError, AnalysisWarning> for SemanticAnalyser<'_> {
    type DiagnosticsStore = AnalyserDiagnostics;

    fn store(&self) -> &Self::DiagnosticsStore {
        &self.diagnostics
    }

    fn store_mut(&mut self) -> &mut Self::DiagnosticsStore {
        &mut self.diagnostics
    }

    fn add_error(&mut self, error: AnalysisError) {
        self.diagnostics.errors.push(error);
    }

    fn add_warning(&mut self, warning: AnalysisWarning) {
        self.store_mut().warnings.push(warning);
    }

    fn has_errors(&self) -> bool {
        !self.store().errors.is_empty()
    }

    fn has_warnings(&self) -> bool {
        !self.store().warnings.is_empty()
    }

    fn into_reports(self) -> Vec<Report> {
        self.diagnostics
            .errors
            .into_iter()
            .map(|err| err.into())
            .chain(self.diagnostics.warnings.into_iter().map(|warn| warn.into()))
            .collect()
    }

    fn into_diagnostics(self) -> (Vec<AnalysisError>, Vec<AnalysisWarning>) {
        (self.diagnostics.errors, self.diagnostics.warnings)
    }

    fn merge(&mut self, other: impl Diagnostics<AnalysisError, AnalysisWarning>) {
        let (errors, warnings) = other.into_diagnostics();

        self.diagnostics.errors.extend(errors);
        self.diagnostics.warnings.extend(warnings);
    }
}
