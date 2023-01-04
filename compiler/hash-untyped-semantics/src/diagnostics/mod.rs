//! Hash AST semantic passes diagnostic definitions and logic.

use hash_ast::ast::AstNodeId;
use hash_reporting::{diagnostic::Diagnostics, report::Report, reporter::Reports};

use self::{error::AnalysisError, warning::AnalysisWarning};
use crate::analysis::SemanticAnalyser;

pub(crate) mod directives;
pub(crate) mod error;
pub(crate) mod warning;

/// A representation of either a [AnalysisWarning] or [AnalysisError]. This
/// is used when they are accumulated and converted into reports at the end.
pub enum AnalysisDiagnostic {
    /// Warnings that are emitted by the analysis pass.
    Warning(AnalysisWarning),
    /// Errors that are emitted by the analysis pass.
    Error(AnalysisError),
}

impl AnalysisDiagnostic {
    /// Get the associated [AstNodeId] with the [AnalysisDiagnostic].
    pub(crate) fn id(&self) -> AstNodeId {
        match self {
            AnalysisDiagnostic::Warning(w) => w.id(),
            AnalysisDiagnostic::Error(e) => e.id(),
        }
    }
}

impl From<AnalysisDiagnostic> for Reports {
    fn from(diagnostic: AnalysisDiagnostic) -> Self {
        match diagnostic {
            AnalysisDiagnostic::Warning(w) => w.into(),
            AnalysisDiagnostic::Error(e) => e.into(),
        }
    }
}

/// Store [SemanticAnalyser] diagnostics which can be errors or warnings.
#[derive(Default)]
pub struct AnalyserDiagnostics {
    /// Any diagnostics that the [SemanticAnalyser] produces.
    pub(crate) items: Vec<AnalysisDiagnostic>,
}

impl Diagnostics<AnalysisError, AnalysisWarning> for SemanticAnalyser<'_> {
    type DiagnosticsStore = AnalyserDiagnostics;

    fn diagnostic_store(&self) -> &Self::DiagnosticsStore {
        &self.diagnostics
    }

    fn add_error(&mut self, error: AnalysisError) {
        self.diagnostics.items.push(AnalysisDiagnostic::Error(error));
    }

    fn add_warning(&mut self, warning: AnalysisWarning) {
        self.diagnostics.items.push(AnalysisDiagnostic::Warning(warning));
    }

    fn has_errors(&self) -> bool {
        !self.diagnostics.items.iter().any(|d| matches!(d, AnalysisDiagnostic::Error(_)))
    }

    fn has_warnings(&self) -> bool {
        !self.diagnostics.items.iter().any(|d| matches!(d, AnalysisDiagnostic::Warning(_)))
    }

    fn into_reports(self) -> Vec<Report> {
        self.diagnostics.items.into_iter().flat_map(Reports::from).collect()
    }

    fn into_diagnostics(self) -> (Vec<AnalysisError>, Vec<AnalysisWarning>) {
        let mut errors = vec![];
        let mut warnings = vec![];

        for item in self.diagnostics.items.into_iter() {
            match item {
                AnalysisDiagnostic::Warning(w) => warnings.push(w),
                AnalysisDiagnostic::Error(e) => errors.push(e),
            }
        }

        (errors, warnings)
    }

    fn merge_diagnostics(&mut self, other: impl Diagnostics<AnalysisError, AnalysisWarning>) {
        let (errors, warnings) = other.into_diagnostics();

        self.diagnostics.items.extend(errors.into_iter().map(AnalysisDiagnostic::Error));
        self.diagnostics.items.extend(warnings.into_iter().map(AnalysisDiagnostic::Warning));
    }
}
