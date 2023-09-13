use hash_ast::node_map::{HasNodeMap, NodeMap};
use hash_exhaustiveness::diagnostics::{ExhaustivenessError, ExhaustivenessWarning};
use hash_pipeline::settings::CompilerSettings;
use hash_reporting::diagnostic::{DiagnosticCellStore, Diagnostics, HasDiagnostics};
use hash_source::entry_point::EntryPointState;
use hash_target::{HasTarget, Target};
use hash_tir::{
    atom_info::{AtomInfoStore, HasAtomInfo},
    context::{Context, HasContext},
    fns::FnDefId,
    mods::ModDefId,
    stores::tir_stores,
};
use hash_typecheck::{errors::TcError, TcEnv};
use once_cell::unsync::OnceCell;

use super::{
    analysis_progress::AnalysisProgress, ast_info::AstInfo, source_info::CurrentSourceInfo,
};
use crate::diagnostics::{error::SemanticError, warning::SemanticWarning};

macro_rules! sem_env {
    ($($(#$hide:ident)? $name:ident: $ty:ident $(<$lt:lifetime> )?),* $(,)?) => {
        /// The typed semantic analysis environment.
        ///
        /// Contains access to stores which contain the typed semantic analysis data.
        /// Also has access to the context, which contains information about the
        /// current scope of variables and facts.
        #[derive(Debug, Copy, Clone)]
        pub struct SemEnv<'tc> {
            $(
                pub $name: &'tc $ty $(<$lt>)?,
            )*
        }

        /// Trait to be implemented for things that want to have access to the
        /// TC environment.
        pub trait AccessToSemEnv {
            fn sem_env(&self) -> &SemEnv;

            $(
                sem_env!(@@ access_to_env_trait ($(#$hide)? $name:$ty));
            )*
        }

        impl<'tc> SemEnv<'tc> {
            #[allow(clippy::too_many_arguments)]
            pub fn new(
                $(
                    $name: &'tc $ty $(<$lt>)?,
                )*
            ) -> Self {
                Self {
                    $(
                        $name,
                    )*
                }
            }
        }

    };
    (@@ access_to_env_trait (#hide $name:ident: $ty:ident)) => { };
    (@@ access_to_env_trait ($name:ident: $ty:ident)) => {
        fn $name(&self) -> &$ty {
            &self.sem_env().$name
        }
    }
}

pub type DiagnosticsStore = DiagnosticCellStore<SemanticError, SemanticWarning>;
pub type PreludeOrUnset = OnceCell<ModDefId>;
pub type RootModOrUnset = OnceCell<ModDefId>;
pub type EntryPoint = EntryPointState<FnDefId>;

// All the members of the semantic analysis environment.
sem_env! {
    diagnostics: DiagnosticsStore,
    entry_point: EntryPoint,
    ast_info: AstInfo,
    prelude_or_unset: PreludeOrUnset,
    root_mod_or_unset: RootModOrUnset,
    analysis_progress: AnalysisProgress,
    settings: CompilerSettings,
    context: Context,
    node_map: NodeMap,
    current_source_info: CurrentSourceInfo,
}

impl<'tc> AccessToSemEnv for SemEnv<'tc> {
    fn sem_env(&self) -> &SemEnv {
        self
    }
}

impl<'tc> HasDiagnostics for SemEnv<'tc> {
    type Diagnostics = DiagnosticCellStore<SemanticError, SemanticWarning>;
    fn diagnostics(&self) -> &Self::Diagnostics {
        self.diagnostics
    }
}

impl<'tc> HasNodeMap for SemEnv<'tc> {
    fn node_map(&self) -> &hash_ast::node_map::NodeMap {
        self.node_map
    }
}

impl HasAtomInfo for SemEnv<'_> {
    fn atom_info(&self) -> &AtomInfoStore {
        // @@Todo: remove this from the TIR stores
        tir_stores().atom_info()
    }
}

impl HasContext for SemEnv<'_> {
    fn context(&self) -> &Context {
        self.context
    }
}

impl HasTarget for SemEnv<'_> {
    fn target(&self) -> &Target {
        self.settings.target()
    }
}

impl<'tc> TcEnv for SemEnv<'tc> {
    fn convert_tc_error(&self, error: TcError) -> <Self::Diagnostics as Diagnostics>::Error {
        error.into()
    }

    fn convert_exhaustiveness_error(
        &self,
        error: ExhaustivenessError,
    ) -> <<Self as HasDiagnostics>::Diagnostics as Diagnostics>::Error {
        error.into()
    }

    fn convert_exhaustiveness_warning(
        &self,
        warning: ExhaustivenessWarning,
    ) -> <<Self as HasDiagnostics>::Diagnostics as Diagnostics>::Warning {
        warning.into()
    }

    fn entry_point(&self) -> &EntryPointState<FnDefId> {
        self.entry_point
    }

    fn should_monomorphise(&self) -> bool {
        self.settings.semantic_settings.mono_tir
    }

    fn current_source(&self) -> hash_source::SourceId {
        self.current_source_info.source_id()
    }
}

/// A reference to [`SemEnv`] alongside a value.
///
/// This is useful for passing around a reference to the tcenv alongside
/// some value.
pub struct WithSemEnv<'tc, T> {
    sem_env: &'tc SemEnv<'tc>,
    pub value: T,
}

impl<'tc, T> AccessToSemEnv for WithSemEnv<'tc, T> {
    fn sem_env(&self) -> &SemEnv {
        self.sem_env
    }
}

impl<'tc, T> HasDiagnostics for WithSemEnv<'tc, T> {
    type Diagnostics = DiagnosticsStore;
    fn diagnostics(&self) -> &Self::Diagnostics {
        AccessToSemEnv::diagnostics(self)
    }
}

impl<T> HasAtomInfo for WithSemEnv<'_, T> {
    fn atom_info(&self) -> &AtomInfoStore {
        // @@Todo: remove this from the TIR stores
        tir_stores().atom_info()
    }
}

impl<T> HasContext for WithSemEnv<'_, T> {
    fn context(&self) -> &Context {
        self.sem_env.context
    }
}

impl<T> HasTarget for WithSemEnv<'_, T> {
    fn target(&self) -> &Target {
        self.sem_env.settings.target()
    }
}

impl<'tc, T> TcEnv for WithSemEnv<'tc, T> {
    fn convert_tc_error(&self, error: TcError) -> <Self::Diagnostics as Diagnostics>::Error {
        error.into()
    }

    fn convert_exhaustiveness_error(
        &self,
        error: ExhaustivenessError,
    ) -> <<Self as HasDiagnostics>::Diagnostics as Diagnostics>::Error {
        error.into()
    }

    fn convert_exhaustiveness_warning(
        &self,
        warning: ExhaustivenessWarning,
    ) -> <<Self as HasDiagnostics>::Diagnostics as Diagnostics>::Warning {
        warning.into()
    }

    fn entry_point(&self) -> &EntryPointState<FnDefId> {
        AccessToSemEnv::entry_point(self)
    }

    fn should_monomorphise(&self) -> bool {
        self.sem_env.should_monomorphise()
    }

    fn current_source(&self) -> hash_source::SourceId {
        self.sem_env.current_source_info.source_id()
    }
}

impl<'tc, T: Clone> Clone for WithSemEnv<'tc, T> {
    fn clone(&self) -> Self {
        Self { sem_env: self.sem_env, value: self.value.clone() }
    }
}
impl<'tc, T: Copy> Copy for WithSemEnv<'tc, T> {}

impl<'tc, T> WithSemEnv<'tc, T> {
    pub fn new(env: &'tc SemEnv, value: T) -> Self {
        Self { sem_env: env, value }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> WithSemEnv<'tc, U> {
        WithSemEnv { sem_env: self.sem_env, value: f(self.value) }
    }
}

impl<'tc> SemEnv<'tc> {
    /// Attach a value to a [`SemEnv`] reference, creating a
    /// [`WithSemEnv`] value.
    pub fn with<T>(&self, value: T) -> WithSemEnv<T> {
        WithSemEnv::new(self, value)
    }
}

/// Convenience macro for implementing [`AccessToSemEnv`] and friends
/// for a type.
#[macro_export]
macro_rules! impl_access_to_sem_env {
    ($ty:ty) => {
        impl $crate::environment::sem_env::AccessToSemEnv for $ty {
            fn sem_env(&self) -> &$crate::environment::sem_env::SemEnv {
                self.sem_env
            }
        }

        impl hash_reporting::diagnostic::HasDiagnostics for $ty {
            type Diagnostics = hash_reporting::diagnostic::DiagnosticCellStore<
                $crate::diagnostics::error::SemanticError,
                $crate::diagnostics::warning::SemanticWarning,
            >;

            fn diagnostics(&self) -> &Self::Diagnostics {
                $crate::environment::sem_env::AccessToSemEnv::diagnostics(self.sem_env())
            }
        }

        impl hash_typecheck::TcEnv for $ty {
            fn convert_tc_error(
                &self,
                error: hash_typecheck::errors::TcError,
            ) -> <Self::Diagnostics as hash_reporting::diagnostic::Diagnostics>::Error {
                error.into()
            }

            fn convert_exhaustiveness_error(
                &self,
                error: hash_exhaustiveness::diagnostics::ExhaustivenessError,
            ) -> <Self::Diagnostics as hash_reporting::diagnostic::Diagnostics>::Error {
                error.into()
            }

            fn convert_exhaustiveness_warning(
                &self,
                warning: hash_exhaustiveness::diagnostics::ExhaustivenessWarning,
            ) -> <Self::Diagnostics as hash_reporting::diagnostic::Diagnostics>::Warning {
                warning.into()
            }

            fn entry_point(
                &self,
            ) -> &hash_source::entry_point::EntryPointState<hash_tir::fns::FnDefId> {
                $crate::environment::sem_env::AccessToSemEnv::entry_point(self)
            }

            fn should_monomorphise(&self) -> bool {
                self.sem_env().should_monomorphise()
            }
        }
    };
}
