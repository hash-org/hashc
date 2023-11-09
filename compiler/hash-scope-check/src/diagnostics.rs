//! Diagnostics for the scope checker.
use hash_ast::ast::AstNodeId;
use hash_reporting::{
    diagnostic::DiagnosticStore,
    hash_error_codes::error_codes::HashErrorCode,
    reporter::{AddToReporter, Reporter},
};
use hash_source::identifier::Identifier;

/// The diagnostics for the scope checker.
pub type ScopingDiagnostics = DiagnosticStore<ScopingError, ScopingWarning>;

/// An error that occurred during scope checking.
#[derive(Debug, Clone)]
pub enum ScopingError {
    NonSimpleBindingForDefinition { binding_node: AstNodeId, definition_node: AstNodeId },
    SymbolNotFound { symbol: Identifier, referencing_node: AstNodeId },
}

impl AddToReporter for ScopingError {
    /// Format the error and add it to the reporter.
    fn add_to_reporter(&self, reporter: &mut Reporter) {
        match self {
            ScopingError::NonSimpleBindingForDefinition { binding_node, definition_node } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::MismatchingPatBind)
                    .title("cannot pattern match on definitions");

                error.add_span(binding_node.span()).add_info(
                    "tried to pattern match on a definition. Try using a simple binding instead.",
                );
                error
                    .add_span(definition_node.span())
                    .add_info("this is a definition, so it cannot be matched by a pattern.");
            }
            ScopingError::SymbolNotFound { symbol, referencing_node } => {
                let error = reporter
                    .error()
                    .code(HashErrorCode::UnresolvedSymbol)
                    .title(format!("cannot find symbol `{}` in the current scope", symbol));
                error.add_span(referencing_node.span()).add_info(format!(
                    "tried to reference symbol `{}`, which does not exist in this scope.",
                    symbol
                ));
            }
        }
    }
}

/// A warning that occurred during scope checking.
#[derive(Debug, Clone)]
pub enum ScopingWarning {}

impl AddToReporter for ScopingWarning {
    /// Format the warning and add it to the reporter.
    fn add_to_reporter(&self, _reporter: &mut Reporter) {
        match *self {}
    }
}
