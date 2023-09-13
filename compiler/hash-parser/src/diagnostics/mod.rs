//! Hash Parser diagnostic utilities, error and warning definitions.
//! This module contains all of the logic that provides diagnostic
//! capabilities within the parser.
pub(crate) mod error;
pub(crate) mod expected;
pub(crate) mod warning;

use hash_reporting::diagnostic::{DiagnosticCellStore, HasDiagnostics};

use self::{error::ParseError, warning::ParseWarning};
use crate::parser::AstGen;

/// Shorthand for the parser diagnostics.
pub type ParserDiagnostics = DiagnosticCellStore<ParseError, ParseWarning>;

impl<'s> HasDiagnostics for AstGen<'s> {
    type Diagnostics = ParserDiagnostics;

    fn diagnostics(&self) -> &Self::Diagnostics {
        self.diagnostics
    }
}
