//! Definitions for diagnostics that can be emitted
//! during the compiler AST expansion phase.

use hash_ast::ast::AstNodeId;
use hash_reporting::{diagnostic::DiagnosticStore, reporter::Reports};

use self::error::ExpansionError;

pub mod error;

/// @@Future: potentially add warning diagnostics too.
pub type ExpansionWarning = ();

pub type ExpansionDiagnostics = DiagnosticStore<ExpansionError, ExpansionWarning>;

/// Any diagnostics that can be emitted by the expansion phase.
#[derive(Debug)]
pub enum ExpansionDiagnostic {
    /// An error occurred.
    Error(ExpansionError),
}

impl ExpansionDiagnostic {
    pub(crate) fn id(&self) -> AstNodeId {
        match self {
            ExpansionDiagnostic::Error(e) => e.id,
        }
    }
}

impl From<ExpansionError> for ExpansionDiagnostic {
    fn from(error: ExpansionError) -> Self {
        Self::Error(error)
    }
}

impl From<ExpansionDiagnostic> for Reports {
    fn from(diagnostic: ExpansionDiagnostic) -> Self {
        match diagnostic {
            ExpansionDiagnostic::Error(e) => e.into(),
        }
    }
}
