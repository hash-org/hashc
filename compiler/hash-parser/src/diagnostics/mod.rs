//! Hash Parser diagnostic utilities, error and warning definitions.
//! This module contains all of the logic that provides diagnostic
//! capabilities within the parser.
pub(crate) mod error;
pub(crate) mod warning;

use hash_reporting::diagnostic::Diagnostics;
use smallvec::SmallVec;

use self::{error::ParseError, warning::ParseWarning};
use crate::parser::AstGen;

/// Enum representing the kind of statement where type arguments can be expected
/// to be present.
#[derive(Debug, Clone, Copy)]
pub enum TyArgumentKind {
    /// Type arguments at a struct definition.
    Struct,
    /// Type arguments at a enum definition.
    Enum,
}

impl std::fmt::Display for TyArgumentKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TyArgumentKind::Struct => write!(f, "struct"),
            TyArgumentKind::Enum => write!(f, "enumeration"),
        }
    }
}

/// Represents the stored diagnostics within the parser.
#[derive(Default)]
pub struct ParserDiagnostics {
    errors: SmallVec<[ParseError; 2]>,
    warnings: Vec<ParseWarning>,
}

impl<'stream, 'resolver> Diagnostics<ParseError, ParseWarning> for AstGen<'stream, 'resolver> {
    type DiagnosticsStore = ParserDiagnostics;

    fn store(&self) -> &Self::DiagnosticsStore {
        &self.diagnostics
    }

    fn store_mut(&mut self) -> &mut Self::DiagnosticsStore {
        &mut self.diagnostics
    }

    fn add_error(&mut self, error: ParseError) {
        self.store_mut().errors.push(error);
    }

    fn add_warning(&mut self, warning: ParseWarning) {
        self.store_mut().warnings.push(warning);
    }

    fn has_errors(&self) -> bool {
        !self.store().errors.is_empty()
    }

    fn has_warnings(&self) -> bool {
        !self.store().warnings.is_empty()
    }

    fn into_reports(self) -> Vec<hash_reporting::report::Report> {
        self.diagnostics
            .errors
            .into_iter()
            .map(|err| err.into())
            .chain(self.diagnostics.warnings.into_iter().map(|warn| warn.into()))
            .collect()
    }

    fn into_diagnostics(self) -> (Vec<ParseError>, Vec<ParseWarning>) {
        (self.diagnostics.errors.to_vec(), self.diagnostics.warnings)
    }

    fn merge(&mut self, other: impl Diagnostics<ParseError, ParseWarning>) {
        let (errors, warnings) = other.into_diagnostics();

        self.diagnostics.errors.extend(errors);
        self.diagnostics.warnings.extend(warnings);
    }
}
