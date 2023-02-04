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
    let_chains,
    if_let_guard,
    cell_update
)]

use std::cell::RefCell;

use diagnostics::{
    error::{TcError, TcErrorWithStorage},
    warning::{TcWarning, TcWarningWithStorage},
};
use hash_pipeline::{
    interface::{CompilerInterface, CompilerStage},
    settings::{CompilerSettings, CompilerStageKind},
    workspace::Workspace,
    CompilerResult,
};
use hash_reporting::diagnostic::{DiagnosticCellStore, Diagnostics};
use hash_source::{entry_point::EntryPointState, SourceId};
use hash_tir::{
    fmt::PrepareForFormatting,
    new::environment::{
        context::Context, env::Env, source_info::CurrentSourceInfo, stores::Stores,
    },
    storage::{LocalStorage, TyStorage},
};
use hash_utils::stream_less_writeln;
use new::{
    diagnostics::warning::SemanticWarning,
    environment::{
        ast_info::AstInfo,
        tc_env::{AccessToTcEnv, TcEnv},
    },
};
use once_cell::unsync::OnceCell;
use storage::{
    cache::Cache, exhaustiveness::ExhaustivenessStorage, sources::CheckedSources, AccessToStorage,
    StorageRef,
};
use traverse::visitor::TcVisitor;

use crate::new::diagnostics::error::SemanticError;

pub mod diagnostics;
pub mod exhaustiveness;
pub mod new;
pub mod ops;
pub mod storage;
pub mod traverse;

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

    /// The new typechecking environment
    pub _new_stores: Stores,
    pub _new_ast_info: AstInfo,
    pub _new_diagnostic: DiagnosticCellStore<SemanticError, SemanticWarning>,
    pub _new_ctx: Context,
}

impl Typechecker {
    pub fn new() -> Self {
        Self {
            checked_sources: CheckedSources::new(),
            exhaustiveness_storage: ExhaustivenessStorage::default(),
            diagnostics_store: DiagnosticCellStore::default(),
            cache: Cache::new(),
            _new_stores: Stores::new(),
            _new_ctx: Context::new(),
            _new_diagnostic: DiagnosticCellStore::default(),
            _new_ast_info: AstInfo::new(),
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
        CompilerStageKind::Typecheck
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

        let TyStorage { local, global, ref mut entry_point_state } = ty_storage;

        let current_source_info = CurrentSourceInfo { source_id: entry_point };

        let env = Env::new(
            &self._new_stores,
            &self._new_ctx,
            &workspace.node_map,
            &workspace.source_map,
            &current_source_info,
        );

        let primitives = OnceCell::new();
        let intrinsics = OnceCell::new();
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
            _new: TcEnv::new(
                &env,
                &self._new_diagnostic,
                &self._new_ast_info,
                &primitives,
                &intrinsics,
            ),
        };

        // @@Hack: for now we use the `USE_NEW_TC` env variable to switch between the
        // old and new typechecker. This will be removed once the new
        // typechecker is complete.

        if std::env::var_os("USE_NEW_TC").is_some() {
            let tc_visitor = new::passes::TcVisitor::new(&storage._new);
            tc_visitor.visit_source();
            if tc_visitor.tc_env().diagnostics().has_errors() {
                let (errors, _warnings) = tc_visitor.tc_env().diagnostics().into_diagnostics();
                return Err(tc_visitor.tc_env().with(&SemanticError::Compound { errors }).into());
            }
        } else {
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
                    stream_less_writeln!(
                        "{}",
                        source_term.for_formatting(storage.global_storage())
                    );
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
        }

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
