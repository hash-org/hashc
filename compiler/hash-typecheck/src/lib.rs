//! The Hash typechecker.
//!
//! This brings light to the world by ensuring the correctness of the crude and
//! dangerous Hash program that is given as input to the compiler.
//!
//! @@Docs(kontheocharis): write docs about the stages of the typechecker.

#![feature(
    decl_macro,
    slice_pattern,
    option_result_contains,
    let_else,
    let_chains,
    if_let_guard
)]

use diagnostics::DiagnosticsStore;
use hash_pipeline::{traits::Tc, CompilerResult};
use hash_reporting::diagnostic::Diagnostics;
use hash_source::SourceId;
use hash_types::{
    fmt::PrepareForFormatting,
    storage::{GlobalStorage, LocalStorage},
};
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
pub struct TcImpl;

/// Contains global typechecker state, used for the [Tc] implementation below.
#[derive(Debug)]
pub struct TcState {
    /// Map representing a relation between the typechecked module and it's
    /// relevant [SourceId].
    pub checked_sources: CheckedSources,

    /// The shared typechecking context throughout the typechecking process.
    pub global_storage: GlobalStorage,

    /// The shared exhaustiveness checking data store.
    pub exhaustiveness_storage: ExhaustivenessStorage,

    pub prev_local_storage: LocalStorage,

    /// Share typechecking diagnostics
    pub diagnostics_store: DiagnosticsStore,

    /// Typechecking cache, contains useful mappings for a variety of
    /// operations.
    pub cache: Cache,
}

impl TcState {
    /// Create a new [TcState].
    pub fn new() -> Self {
        let source_id = SourceId::default();
        let global_storage = GlobalStorage::new();
        let local_storage = LocalStorage::new(&global_storage, source_id);
        Self {
            checked_sources: CheckedSources::new(),
            global_storage,
            exhaustiveness_storage: ExhaustivenessStorage::default(),
            prev_local_storage: local_storage,
            diagnostics_store: DiagnosticsStore::default(),
            cache: Cache::new(),
        }
    }
}

impl Default for TcState {
    fn default() -> Self {
        Self::new()
    }
}

impl Tc<'_> for TcImpl {
    type State = TcState;

    /// Make a [Self::State] for [TcImpl]. Internally, this creates
    /// a new [GlobalStorage] and [LocalStorage] with a default
    /// [SourceId]. This is safe because both methods that are used
    /// to visit any source kind, will overwrite the stored [SourceId]
    /// to the `entry_point`.
    fn make_state(&mut self) -> CompilerResult<Self::State> {
        Ok(TcState::new())
    }

    fn check_interactive(
        &mut self,
        id: hash_source::InteractiveId,
        workspace: &hash_pipeline::sources::Workspace,
        state: &mut Self::State,
        _job_params: &hash_pipeline::settings::CompilerJobParams,
    ) -> CompilerResult<()> {
        // We need to set the interactive-id to update the current local-storage `id`
        // value
        state.prev_local_storage.set_current_source(SourceId::Interactive(id));

        // Instantiate a visitor with the source and visit the source, using the
        // previous local storage.
        let storage = StorageRef {
            global_storage: &state.global_storage,
            checked_sources: &state.checked_sources,
            exhaustiveness_storage: &state.exhaustiveness_storage,
            local_storage: &state.prev_local_storage,
            source_map: &workspace.source_map,
            diagnostics_store: &state.diagnostics_store,
            cache: &state.cache,
        };
        let mut tc_visitor = TcVisitor::new_in_source(storage.storages(), workspace.node_map());

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
        sources: &hash_pipeline::sources::Workspace,
        state: &mut Self::State,
        _job_params: &hash_pipeline::settings::CompilerJobParams,
    ) -> CompilerResult<()> {
        // Instantiate a visitor with the source and visit the source, using a new local
        // storage.
        let local_storage = LocalStorage::new(&state.global_storage, SourceId::Module(id));

        let storage = StorageRef {
            global_storage: &state.global_storage,
            checked_sources: &state.checked_sources,
            exhaustiveness_storage: &state.exhaustiveness_storage,
            local_storage: &local_storage,
            source_map: &sources.source_map,
            diagnostics_store: &state.diagnostics_store,
            cache: &state.cache,
        };

        let mut tc_visitor = TcVisitor::new_in_source(storage.storages(), sources.node_map());

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
