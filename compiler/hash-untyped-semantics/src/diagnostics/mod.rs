//! Hash AST semantic passes diagnostic definitions and logic.

use derive_more::From;
use hash_ast::ast::AstNodeId;
use hash_reporting::{
    diagnostic::{DiagnosticStore, HasDiagnosticsMut},
    reporter::Reports,
};

use self::{error::AnalysisError, warning::AnalysisWarning};
use crate::analysis::SemanticAnalyser;

pub(crate) mod error;
pub(crate) mod warning;

/// A representation of either a [AnalysisWarning] or [AnalysisError]. This
/// is used when they are accumulated and converted into reports at the end.
#[derive(From)]
pub enum AnalysisDiagnostic {
    /// Warnings that are emitted by the analysis pass.
    #[from]
    Warning(AnalysisWarning),
    /// Errors that are emitted by the analysis pass.
    #[from]
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
    pub(crate) store: DiagnosticStore<AnalysisError, AnalysisWarning>,
}

impl HasDiagnosticsMut for SemanticAnalyser {
    type Diagnostics = DiagnosticStore<AnalysisError, AnalysisWarning>;

    fn diagnostics(&mut self) -> &mut Self::Diagnostics {
        &mut self.diagnostics.store
    }
}
