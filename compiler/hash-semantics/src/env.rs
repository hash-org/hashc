use hash_ast::node_map::HasNodeMap;
use hash_ir::HasIrCtx;
use hash_layout::HasLayout;
use hash_pipeline::settings::HasCompilerSettings;
use hash_reporting::diagnostic::{Diagnostics, HasDiagnostics};
use hash_source::entry_point::EntryPointState;
use hash_target::HasTarget;
use hash_tir::tir::{FnDefId, ModDefId};
use hash_tir_utils::lower::HasTyCache;
use hash_utils::timing::HasMetrics;
use once_cell::sync::OnceCell;

use crate::{
    diagnostics::definitions::{SemanticError, SemanticResult, SemanticWarning},
    storage::SemanticStorage,
};

pub trait HasSemanticDiagnostics: HasDiagnostics<Diagnostics = Self::SemanticDiagnostics> {
    type SemanticDiagnostics: Diagnostics<Error = SemanticError, Warning = SemanticWarning>;
}

pub trait SemanticEnv:
    HasNodeMap
    + HasMetrics
    + HasSemanticDiagnostics
    + HasCompilerSettings
    + HasTarget
    + HasLayout
    + HasIrCtx
    + HasTyCache
{
    fn storage(&self) -> &SemanticStorage;
    fn storage_mut(&mut self) -> &mut SemanticStorage;

    fn prelude_mod(&self) -> &OnceCell<ModDefId> {
        &self.storage().distinguished_items.prelude_mod
    }

    fn entry_point(&self) -> &EntryPointState<FnDefId> {
        &self.storage().distinguished_items.entry_point
    }

    fn root_mod(&self) -> ModDefId {
        self.storage().distinguished_items.root_mod()
    }

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
