use std::cell::RefCell;

use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::{CompilerSettings, CompilerStageKind},
    workspace::Workspace,
    CompilerResult,
};
use hash_reporting::diagnostic::{DiagnosticCellStore, Diagnostics};
use hash_source::{entry_point::EntryPointState, SourceId};
use hash_tir::old::{
    fmt::PrepareForFormatting,
    storage::{LocalStorage, TyStorage},
};
use hash_utils::{log, stream_less_writeln};

use crate::old::{
    diagnostics::{
        error::{TcError, TcErrorWithStorage},
        warning::{TcWarning, TcWarningWithStorage},
    },
    storage::{
        cache::Cache, exhaustiveness::ExhaustivenessStorage, sources::CheckedSources,
        AccessToStorage, StorageRef,
    },
    traverse::visitor::TcVisitor,
};

pub mod diagnostics;
pub mod exhaustiveness;
pub mod ops;
pub mod storage;
pub mod traverse;

// @@Remove: old code from compiler/hash-semantics/src/lib.rs

/// The Hash typechecker compiler stage. This will walk the AST, and
/// typecheck all items within the current compiler [Workspace].
#[derive(Default)]
pub struct Typechecker {
    /// Map representing a relation between the typechecked module and it's
    /// relevant [SourceId].
    pub checked_sources: CheckedSources,

    /// The shared exhaustiveness checking data store.
    pub exhaustiveness_storage: ExhaustivenessStorage,

    /// Share typechecking diagnostics
    pub diagnostics_store: DiagnosticCellStore<TcError, TcWarning>,

    /// Typechecking cache, contains useful mappings for a variety of
    /// operations.
    pub cache: Cache,
}

impl Typechecker {
    pub fn new() -> Self {
        Self {
            checked_sources: CheckedSources::new(),
            exhaustiveness_storage: ExhaustivenessStorage::default(),
            diagnostics_store: DiagnosticCellStore::default(),
            cache: Cache::new(),
        }
    }
}

/// The [TypecheckingCtx] represents all of the information that is
/// required by the [Typechecker] to perform all typechecking operations.
pub struct TypecheckingCtx<'tc> {
    /// The workspace. This is used to retrieve the AST and other
    /// information about the source.
    pub workspace: &'tc Workspace,

    /// The settings of the compiler.
    pub settings: &'tc CompilerSettings,

    /// The typechecking storage. This is used to store the typechecked
    /// items.
    pub ty_storage: &'tc mut TyStorage,
}

/// The typechecking context query. This is used to retrieve the
/// [TyStorage] and [Workspace] from the compiler context.
pub trait TypecheckingCtxQuery: CompilerInterface {
    fn data(&mut self) -> TypecheckingCtx;
}

impl<Ctx: TypecheckingCtxQuery> CompilerStage<Ctx> for Typechecker {
    fn kind(&self) -> CompilerStageKind {
        CompilerStageKind::Analysis
    }

    fn run(&mut self, entry_point: SourceId, ctx: &mut Ctx) -> CompilerResult<()> {
        let TypecheckingCtx { workspace, ty_storage, settings } = ctx.data();

        // Clear the diagnostics store of any previous errors and warnings. This needs
        // to be done for both the `interactive` pipeline and the `module`
        // pipeline.
        self.diagnostics_store.clear_diagnostics();

        // We need to set the interactive-id to update the current local-storage `id`
        // value, but for modules, we create a new local storage.
        if entry_point.is_interactive() {
            ty_storage.local.set_current_source(entry_point);
        } else {
            ty_storage.local = LocalStorage::new(&ty_storage.global, entry_point);
        }

        let TyStorage { local, global, entry_point_state } = ty_storage;

        let ep_state = RefCell::new(EntryPointState::new());

        // Instantiate a visitor with the source and visit the source, using the
        // previous local storage.
        let storage = StorageRef {
            global_storage: global,
            local_storage: local,
            checked_sources: &self.checked_sources,
            exhaustiveness_storage: &self.exhaustiveness_storage,
            diagnostics_store: &self.diagnostics_store,
            cache: &self.cache,
            settings,
            workspace,
            entry_point_state: &ep_state,
        };

        // @@Hack: for now we use the `USE_NEW_TC` env variable to switch between the
        // old and new typechecker. This will be removed once the new
        // typechecker is complete.

        let tc_visitor = TcVisitor::new_in_source(storage.storages(), &workspace.node_map);
        match tc_visitor.visit_source() {
            Err(err) => {
                tc_visitor.diagnostics().add_error(err);
            }
            Ok(source_term)
                if !tc_visitor.diagnostics().has_errors() && entry_point.is_interactive() =>
            {
                // @@Cmdline: make this a configurable behaviour through a cmd-arg.
                // Print the result if no errors
                stream_less_writeln!("{}", source_term.for_formatting(storage.global_storage()));
            }
            Ok(_) => {}
        }

        // If there are diagnostics that were generated or the result itself returned
        // an error, then we should return those errors, otherwise print the inferred
        // term.
        if tc_visitor.diagnostics().has_diagnostics() {
            return Err(tc_visitor.diagnostics().into_reports(
                |err| TcErrorWithStorage::new(err, storage).into(),
                |warning| TcWarningWithStorage::new(warning, storage).into(),
            ));
        }

        // @@Hack: we now take the entry_point state from the typechecker, and then
        // set our own entry as the new entry point state.
        *entry_point_state = ep_state.into_inner();

        Ok(())
    }

    /// We use the cleanup function to report on cache metrics for the
    /// typechecker.
    fn cleanup(&mut self, _entry_point: SourceId, _stage_data: &mut Ctx) {
        log::debug!(
            "tc cache metrics:\n{: <8}: {}\n{: <8}: {}\n",
            "validate",
            self.cache.validation_store.metrics(),
            "infer",
            self.cache.inference_store.metrics()
        );
    }
}
