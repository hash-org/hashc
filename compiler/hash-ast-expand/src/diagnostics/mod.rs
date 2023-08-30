//! Definitions for diagnostics that can be emitted
//! during the compiler AST expansion phase.

use hash_ast::ast::AstNodeId;
use hash_reporting::{diagnostic::DiagnosticStore, reporter::Reports};

use self::{error::ExpansionError, warning::ExpansionWarning};

pub mod error;
pub mod warning;

pub(crate) struct ExpansionDiagnostics {
    pub(crate) store: DiagnosticStore<ExpansionError, ExpansionWarning>,
}

impl ExpansionDiagnostics {
    /// Create a new [ExpansionDiagnostics].
    pub fn new() -> Self {
        Self { store: DiagnosticStore::new() }
    }
}

/// Any diagnostics that can be emitted by the expansion phase.
#[derive(Debug)]
pub enum ExpansionDiagnostic {
    /// An error occurred.
    Error(ExpansionError),

    /// An emitted warning.
    Warning(ExpansionWarning),
}

impl ExpansionDiagnostic {
    pub(crate) fn id(&self) -> AstNodeId {
        match self {
            ExpansionDiagnostic::Error(e) => e.id,
            ExpansionDiagnostic::Warning(e) => e.id,
        }
    }
}

impl From<ExpansionError> for ExpansionDiagnostic {
    fn from(error: ExpansionError) -> Self {
        Self::Error(error)
    }
}

impl From<ExpansionWarning> for ExpansionDiagnostic {
    fn from(warning: ExpansionWarning) -> Self {
        Self::Warning(warning)
    }
}

impl From<ExpansionDiagnostic> for Reports {
    fn from(diagnostic: ExpansionDiagnostic) -> Self {
        match diagnostic {
            ExpansionDiagnostic::Error(e) => e.into(),
            ExpansionDiagnostic::Warning(e) => e.into(),
        }
    }
}
