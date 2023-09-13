use hash_pipeline::settings::{CompilerSettings, HasCompilerSettings};
use hash_reporting::diagnostic::HasDiagnostics;
use hash_source::{entry_point::EntryPointState, SourceId};
use hash_target::{HasTarget, Target};
use hash_tir::{
    atom_info::{AtomInfoStore, HasAtomInfo},
    context::{Context, HasContext},
    stores::tir_stores,
};
use hash_typecheck::{HasTcDiagnostics, TcEnv};

use crate::{
    diagnostics::definitions::{SemanticError, SemanticWarning},
    env::SemanticEnv,
};

/// This is a wrapper around the semantic environment and some extra
/// data which implements the [`TcEnv`] trait, giving access to typechecking.
pub struct TcEnvImpl<'env, E: SemanticEnv> {
    env: &'env E,
    source: SourceId,
    context: Context,
}

impl<'env, E: SemanticEnv> TcEnvImpl<'env, E> {
    pub fn new(env: &'env E, source: SourceId) -> Self {
        Self { env, source, context: Context::new() }
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

impl<E: SemanticEnv> HasCompilerSettings for TcEnvImpl<'_, E> {
    fn settings(&self) -> &CompilerSettings {
        self.env.settings()
    }
}

impl<E: SemanticEnv> HasContext for TcEnvImpl<'_, E> {
    fn context(&self) -> &Context {
        &self.context
    }
}

impl<E: SemanticEnv> HasAtomInfo for TcEnvImpl<'_, E> {
    fn atom_info(&self) -> &AtomInfoStore {
        tir_stores().atom_info()
    }
}

impl<E: SemanticEnv> TcEnv for TcEnvImpl<'_, E> {
    fn entry_point(&self) -> &EntryPointState<hash_tir::fns::FnDefId> {
        self.env.entry_point()
    }

    fn current_source(&self) -> SourceId {
        self.source
    }
}
