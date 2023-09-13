use hash_ast::node_map::HasNodeMap;
use hash_reporting::diagnostic::{Diagnostics, HasDiagnostics};

use crate::{
    diagnostics::definitions::{SemanticError, SemanticResult, SemanticWarning},
    storage::SemanticStorage,
};

pub trait HasSemanticDiagnostics: HasDiagnostics<Diagnostics = Self::SemanticDiagnostics> {
    type SemanticDiagnostics: Diagnostics<Error = SemanticError, Warning = SemanticWarning>;
}

pub trait SemanticEnv: HasNodeMap + HasSemanticDiagnostics {
    fn storage(&self) -> &SemanticStorage;
    fn storage_mut(&mut self) -> &mut SemanticStorage;

    /// If the result is an error, add it to the diagnostics and return `None`.
    fn try_or_add_error<T>(&self, result: SemanticResult<T>) -> Option<T> {
        match result {
            Ok(t) => Some(t),
            Err(error) => {
                self.diagnostics().add_error(error);
                None
            }
        }
    }
}
