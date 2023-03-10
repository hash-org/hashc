use hash_intrinsics::{
    intrinsics::{AccessToIntrinsics, DefinedIntrinsics},
    primitives::{AccessToPrimitives, DefinedPrimitives},
};
use hash_reporting::diagnostic::{AccessToDiagnostics, DiagnosticCellStore, Diagnostics};
use hash_source::entry_point::EntryPointState;
// @@Docs
use hash_tir::{
    environment::env::{AccessToEnv, Env},
    fns::FnDefId,
    mods::ModDefId,
};
use hash_typecheck::{errors::TcError, AccessToTypechecking};
use once_cell::unsync::OnceCell;

use super::analysis_progress::AnalysisProgress;
use crate::{
    diagnostics::{error::SemanticError, warning::SemanticWarning},
    ops::bootstrap::{DefinedIntrinsicsOrUnset, DefinedPrimitivesOrUnset},
    Flags,
};

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
        pub trait AccessToSemEnv: AccessToEnv {
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
    #hide env: Env<'tc>,
    diagnostics: DiagnosticsStore,
    entry_point: EntryPoint,
    prelude_or_unset: PreludeOrUnset,
    primitives_or_unset: DefinedPrimitivesOrUnset,
    intrinsics_or_unset: DefinedIntrinsicsOrUnset,
    root_mod_or_unset: RootModOrUnset,
    analysis_progress: AnalysisProgress,
    flags: Flags,
}

impl<'tc> AccessToSemEnv for SemEnv<'tc> {
    fn sem_env(&self) -> &SemEnv {
        self
    }
}

impl<'tc> AccessToEnv for SemEnv<'tc> {
    fn env(&self) -> &Env {
        self.env
    }
}

impl<'tc> AccessToPrimitives for SemEnv<'tc> {
    fn primitives(&self) -> &DefinedPrimitives {
        match self.primitives_or_unset().get() {
            Some(primitives) => primitives,
            None => panic!("Tried to get primitives but they are not set yet"),
        }
    }
}

impl<'tc> AccessToIntrinsics for SemEnv<'tc> {
    fn intrinsics(&self) -> &DefinedIntrinsics {
        match self.intrinsics_or_unset().get() {
            Some(intrinsics) => intrinsics,
            None => panic!("Tried to get intrinsics but they are not set yet"),
        }
    }
}

impl<'tc> AccessToDiagnostics for SemEnv<'tc> {
    type Diagnostics = DiagnosticCellStore<SemanticError, SemanticWarning>;
    fn diagnostics(&self) -> &Self::Diagnostics {
        self.diagnostics
    }
}

impl<'tc> AccessToTypechecking for SemEnv<'tc> {
    fn convert_tc_error(&self, error: TcError) -> <Self::Diagnostics as Diagnostics>::Error {
        error.into()
    }

    fn entry_point(&self) -> &EntryPointState<FnDefId> {
        self.entry_point
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

impl<'tc, T> AccessToEnv for WithSemEnv<'tc, T> {
    fn env(&self) -> &Env {
        self.sem_env.env()
    }
}

impl<'tc, T> AccessToPrimitives for WithSemEnv<'tc, T> {
    fn primitives(&self) -> &DefinedPrimitives {
        self.sem_env.primitives()
    }
}

impl<'tc, T> AccessToIntrinsics for WithSemEnv<'tc, T> {
    fn intrinsics(&self) -> &DefinedIntrinsics {
        self.sem_env.intrinsics()
    }
}

impl<'tc, T> AccessToDiagnostics for WithSemEnv<'tc, T> {
    type Diagnostics = DiagnosticsStore;
    fn diagnostics(&self) -> &Self::Diagnostics {
        AccessToSemEnv::diagnostics(self)
    }
}

impl<'tc, T> AccessToTypechecking for WithSemEnv<'tc, T> {
    fn convert_tc_error(&self, error: TcError) -> <Self::Diagnostics as Diagnostics>::Error {
        error.into()
    }

    fn entry_point(&self) -> &EntryPointState<FnDefId> {
        AccessToSemEnv::entry_point(self)
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

        impl hash_tir::environment::env::AccessToEnv for $ty {
            fn env(&self) -> &hash_tir::environment::env::Env {
                self.sem_env().env()
            }
        }

        impl hash_intrinsics::primitives::AccessToPrimitives for $ty {
            fn primitives(&self) -> &hash_intrinsics::primitives::DefinedPrimitives {
                self.sem_env().primitives()
            }
        }

        impl hash_intrinsics::intrinsics::AccessToIntrinsics for $ty {
            fn intrinsics(&self) -> &hash_intrinsics::intrinsics::DefinedIntrinsics {
                self.sem_env().intrinsics()
            }
        }

        impl hash_reporting::diagnostic::AccessToDiagnostics for $ty {
            type Diagnostics = hash_reporting::diagnostic::DiagnosticCellStore<
                $crate::diagnostics::error::SemanticError,
                $crate::diagnostics::warning::SemanticWarning,
            >;

            fn diagnostics(&self) -> &Self::Diagnostics {
                $crate::environment::sem_env::AccessToSemEnv::diagnostics(self.sem_env())
            }
        }

        impl hash_typecheck::AccessToTypechecking for $ty {
            fn convert_tc_error(
                &self,
                error: hash_typecheck::errors::TcError,
            ) -> <Self::Diagnostics as hash_reporting::diagnostic::Diagnostics>::Error {
                error.into()
            }

            fn entry_point(
                &self,
            ) -> &hash_source::entry_point::EntryPointState<hash_tir::fns::FnDefId> {
                $crate::environment::sem_env::AccessToSemEnv::entry_point(self)
            }
        }
    };
}
