use hash_ir::{HasIrCtx, IrCtx};
use hash_pipeline::settings::{CompilerSettings, HasCompilerSettings};
use hash_reporting::diagnostic::HasDiagnostics;
use hash_repr::{compute::LayoutComputer, HasLayout};
use hash_source::{entry_point::EntryPointState, SourceId};
use hash_target::{HasTarget, Target};
use hash_tir::{
    atom_info::{AtomInfoStore, HasAtomInfo},
    stores::tir_stores,
    tir::FnDefId,
};
use hash_tir_utils::lower::{HasTyCache, TyCache};
use hash_typecheck::env::{HasTcDiagnostics, TcEnv};
use hash_utils::timing::{CellStageMetrics, HasMetrics};

use crate::{
    diagnostics::definitions::{SemanticError, SemanticWarning},
    env::SemanticEnv,
};

/// This is a wrapper around the semantic environment and some extra
/// data which implements the [`TcEnv`] trait, giving access to typechecking.
pub struct TcEnvImpl<'env, E: SemanticEnv> {
    env: &'env E,
    source: SourceId,
}

impl<'env, E: SemanticEnv> TcEnvImpl<'env, E> {
    pub fn new(env: &'env E, source: SourceId) -> Self {
        Self { env, source }
    }
}

impl<E: SemanticEnv> HasMetrics for TcEnvImpl<'_, E> {
    fn metrics(&self) -> &CellStageMetrics {
        self.env.metrics()
    }
}

impl<E: SemanticEnv> HasTcDiagnostics for TcEnvImpl<'_, E> {
    type ForeignError = SemanticError;
    type ForeignWarning = SemanticWarning;
    type TcDiagnostics = E::SemanticDiagnostics;
}

impl<E: SemanticEnv> HasDiagnostics for TcEnvImpl<'_, E> {
    type Diagnostics = E::SemanticDiagnostics;
    fn diagnostics(&self) -> &Self::Diagnostics {
        self.env.diagnostics()
    }
}

impl<E: SemanticEnv> HasTarget for TcEnvImpl<'_, E> {
    fn target(&self) -> &Target {
        self.env.target()
    }
}

impl<E: SemanticEnv> HasLayout for TcEnvImpl<'_, E> {
    fn layout_computer(&self) -> LayoutComputer {
        self.env.layout_computer()
    }
}

impl<E: SemanticEnv> HasIrCtx for TcEnvImpl<'_, E> {
    fn ir_ctx(&self) -> &IrCtx {
        self.env.ir_ctx()
    }
}

impl<E: SemanticEnv> HasTyCache for TcEnvImpl<'_, E> {
    fn repr_ty_cache(&self) -> &TyCache {
        &self.env.storage().repr_ty_cache
    }
}

impl<E: SemanticEnv> HasCompilerSettings for TcEnvImpl<'_, E> {
    fn settings(&self) -> &CompilerSettings {
        self.env.settings()
    }
}

impl<E: SemanticEnv> HasAtomInfo for TcEnvImpl<'_, E> {
    fn atom_info(&self) -> &AtomInfoStore {
        tir_stores().atom_info()
    }
}

impl<E: SemanticEnv> TcEnv for TcEnvImpl<'_, E> {
    fn entry_point(&self) -> &EntryPointState<FnDefId> {
        self.env.entry_point()
    }

    fn current_source(&self) -> SourceId {
        self.source
    }
}
