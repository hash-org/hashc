//! The Hash typechecker.
//!
//! This brings light to the world by ensuring the correctness of the crude and
//! dangerous Hash program that is given as input to the compiler.
//!
//! @@Docs(kontheocharis): write docs about the stages of the typechecker.

#![feature(decl_macro, slice_pattern, option_result_contains, let_chains, if_let_guard)]

use diagnostics::DiagnosticsStore;
use hash_pipeline::{sources::TyStorage, traits::Tc, CompilerResult};
use hash_reporting::diagnostic::Diagnostics;
use hash_source::SourceId;
use hash_types::{fmt::PrepareForFormatting, storage::LocalStorage};
use ops::AccessToOps;
use storage::{
    cache::Cache, exhaustiveness::ExhaustivenessStorage, sources::CheckedSources, AccessToStorage,
    StorageRef,
};
use traverse::visitor::TcVisitor;

pub mod diagnostics;
pub mod exhaustiveness;
pub mod ops;
pub mod storage;
pub mod traverse;

/// The entry point of the typechecker.
pub struct Typechecker {
    /// Map representing a relation between the typechecked module and it's
    /// relevant [SourceId].
    pub checked_sources: CheckedSources,

    /// The shared exhaustiveness checking data store.
    pub exhaustiveness_storage: ExhaustivenessStorage,

    /// Share typechecking diagnostics
    pub diagnostics_store: DiagnosticsStore,

    /// Typechecking cache, contains useful mappings for a variety of
    /// operations.
    pub cache: Cache,
}

impl Typechecker {
    pub fn new() -> Self {
        Self {
            checked_sources: CheckedSources::new(),
            exhaustiveness_storage: ExhaustivenessStorage::default(),
            diagnostics_store: DiagnosticsStore::default(),
            cache: Cache::new(),
        }
    }
}

impl Default for Typechecker {
    fn default() -> Self {
        Self::new()
    }
}

impl Tc<'_> for Typechecker {
    fn check_interactive(
        &mut self,
        id: hash_source::InteractiveId,
        workspace: &mut hash_pipeline::sources::Workspace,
    ) -> CompilerResult<()> {
        // We need to set the interactive-id to update the current local-storage `id`
        // value
        workspace.ty_storage.local.set_current_source(SourceId::Interactive(id));

        let TyStorage { local, global } = workspace.ty_storage();

        // Instantiate a visitor with the source and visit the source, using the
        // previous local storage.
        let storage = StorageRef {
            global_storage: global,
            local_storage: local,
            checked_sources: &self.checked_sources,
            exhaustiveness_storage: &self.exhaustiveness_storage,
            source_map: &workspace.source_map,
            diagnostics_store: &self.diagnostics_store,
            cache: &self.cache,
        };
        let tc_visitor = TcVisitor::new_in_source(storage.storages(), workspace.node_map());

        match tc_visitor.visit_source() {
            Err(err) => {
                tc_visitor.diagnostics().add_error(err);
            }
            Ok(source_term) if !tc_visitor.diagnostics().has_errors() => {
                // @@Cmdline: make this a configurable behaviour through a cmd-arg.
                // Print the result if no errors
                println!("{}", source_term.for_formatting(storage.global_storage()));
            }
            Ok(_) => {}
        }

        // If there are diagnostics that were generated or the result itself returned
        // an error, then we should return those errors, otherwise print the inferred
        // term.
        if tc_visitor.diagnostics().has_diagnostics() {
            return Err(tc_visitor.diagnostics().into_reports());
        }

        Ok(())
    }

    fn check_module(
        &mut self,
        id: hash_source::ModuleId,
        workspace: &mut hash_pipeline::sources::Workspace,
    ) -> CompilerResult<()> {
        // Instantiate a visitor with the source and visit the source, using a new local
        // storage.
        workspace.ty_storage.local =
            LocalStorage::new(&workspace.ty_storage.global, SourceId::Module(id));

        let storage = StorageRef {
            global_storage: &workspace.ty_storage.global,
            local_storage: &workspace.ty_storage.local,
            checked_sources: &self.checked_sources,
            exhaustiveness_storage: &self.exhaustiveness_storage,
            source_map: &workspace.source_map,
            diagnostics_store: &self.diagnostics_store,
            cache: &self.cache,
        };

        let tc_visitor = TcVisitor::new_in_source(storage.storages(), workspace.node_map());

        if let Err(err) = tc_visitor.visit_source() {
            tc_visitor.diagnostics().add_error(err);
        }

        if tc_visitor.diagnostics().has_diagnostics() {
            Err(tc_visitor.diagnostics().into_reports())
        } else {
            Ok(())
        }
    }
}
