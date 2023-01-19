use std::cell::RefCell;

use hash_intrinsics::{
    intrinsics::{AccessToIntrinsics, DefinedIntrinsics},
    primitives::{AccessToPrimitives, DefinedPrimitives},
};
use hash_reporting::diagnostic::{AccessToDiagnostics, ImmutableDiagnostics};
// @@Docs
use hash_tir::new::environment::env::{AccessToEnv, Env};
use hash_typecheck::{elaboration::ProofState, errors::TcError, AccessToTypechecking};

use super::ast_info::AstInfo;
use crate::new::{
    diagnostics::{error::SemanticError, warning::SemanticWarning},
    ops::bootstrap::{DefinedIntrinsicsOrUnset, DefinedPrimitivesOrUnset},
};

macro_rules! tc_env {
    ($($(#$hide:ident)? $name:ident: $ty:ident $(<$lt:lifetime> )?),* $(,)?) => {
        /// The typed semantic analysis tcenv.
        ///
        /// Contains access to stores which contain the typed semantic analysis data.
        /// Also has access to the context, which contains information about the
        /// current scope of variables and facts.
        #[derive(Debug, Copy, Clone)]
        pub struct TcEnv<'tc> {
            $(
                pub $name: &'tc $ty $(<$lt>)?,
            )*
        }

        /// Trait to be implemented for things that want to have access to the
        /// TC environment.
        pub trait AccessToTcEnv: AccessToEnv {
            fn tc_env(&self) -> &TcEnv;

            $(
                tc_env!(@@ access_to_env_trait ($(#$hide)? $name:$ty));
            )*
        }

        impl<'tc> TcEnv<'tc> {
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
            &self.tc_env().$name
        }
    }
}

type ProofStateRefCell = RefCell<ProofState>;
pub type DiagnosticsStore = ImmutableDiagnostics<SemanticError, SemanticWarning>;

tc_env! {
    #hide env: Env<'tc>,
    diagnostics: DiagnosticsStore,
    ast_info: AstInfo,
    proof_state: ProofStateRefCell,
    primitives_or_unset: DefinedPrimitivesOrUnset,
    intrinsics_or_unset: DefinedIntrinsicsOrUnset,
}

impl<'tc> AccessToTcEnv for TcEnv<'tc> {
    fn tc_env(&self) -> &TcEnv {
        self
    }
}

impl<'tc> AccessToEnv for TcEnv<'tc> {
    fn env(&self) -> &Env {
        self.env
    }
}

impl<'tc> AccessToPrimitives for TcEnv<'tc> {
    fn primitives(&self) -> &DefinedPrimitives {
        match self.primitives_or_unset().get() {
            Some(primitives) => primitives,
            None => panic!("Tried to get primitives but they are not set yet"),
        }
    }
}

impl<'tc> AccessToIntrinsics for TcEnv<'tc> {
    fn intrinsics(&self) -> &DefinedIntrinsics {
        match self.intrinsics_or_unset().get() {
            Some(intrinsics) => intrinsics,
            None => panic!("Tried to get intrinsics but they are not set yet"),
        }
    }
}

impl<'tc> AccessToDiagnostics for TcEnv<'tc> {
    type Error = SemanticError;
    type Warning = SemanticWarning;
    type Diagnostics = ImmutableDiagnostics<Self::Error, Self::Warning>;

    fn diagnostics(&self) -> &ImmutableDiagnostics<Self::Error, Self::Warning> {
        self.diagnostics
    }
}

impl<'tc> AccessToTypechecking for TcEnv<'tc> {
    fn proof_state(&self) -> &RefCell<ProofState> {
        self.proof_state
    }

    fn convert_tc_error(&self, error: TcError) -> Self::Error {
        error.into()
    }
}

/// A reference to [`TcEnv`] alongside a value.
///
/// This is useful for passing around a reference to the tcenv alongside
/// some value.
pub struct WithTcEnv<'tc, T> {
    tc_env: &'tc TcEnv<'tc>,
    pub value: T,
}

impl<'tc, T> AccessToTcEnv for WithTcEnv<'tc, T> {
    fn tc_env(&self) -> &TcEnv {
        self.tc_env
    }
}

impl<'tc, T> AccessToEnv for WithTcEnv<'tc, T> {
    fn env(&self) -> &Env {
        self.tc_env.env()
    }
}

impl<'tc, T> AccessToPrimitives for WithTcEnv<'tc, T> {
    fn primitives(&self) -> &DefinedPrimitives {
        self.tc_env.primitives()
    }
}

impl<'tc, T> AccessToIntrinsics for WithTcEnv<'tc, T> {
    fn intrinsics(&self) -> &DefinedIntrinsics {
        self.tc_env.intrinsics()
    }
}

impl<'tc, T> AccessToDiagnostics for WithTcEnv<'tc, T> {
    type Error = SemanticError;
    type Warning = SemanticWarning;

    type Diagnostics = DiagnosticsStore;
    fn diagnostics(&self) -> &Self::Diagnostics {
        AccessToTcEnv::diagnostics(self)
    }
}

impl<'tc, T> AccessToTypechecking for WithTcEnv<'tc, T> {
    fn proof_state(&self) -> &RefCell<ProofState> {
        self.tc_env.proof_state
    }

    fn convert_tc_error(&self, error: TcError) -> Self::Error {
        error.into()
    }
}

impl<'tc, T: Clone> Clone for WithTcEnv<'tc, T> {
    fn clone(&self) -> Self {
        Self { tc_env: self.tc_env, value: self.value.clone() }
    }
}
impl<'tc, T: Copy> Copy for WithTcEnv<'tc, T> {}

impl<'tc, T> WithTcEnv<'tc, T> {
    pub fn new(env: &'tc TcEnv, value: T) -> Self {
        Self { tc_env: env, value }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> WithTcEnv<'tc, U> {
        WithTcEnv { tc_env: self.tc_env, value: f(self.value) }
    }
}

impl<'tc> TcEnv<'tc> {
    /// Attach a value to a [`TcEnv`] reference, creating a
    /// [`WithTcEnv`] value.
    pub fn with<T>(&self, value: T) -> WithTcEnv<T> {
        WithTcEnv::new(self, value)
    }
}

#[macro_export]
macro_rules! impl_access_to_tc_env {
    ($ty:ty) => {
        impl $crate::new::environment::tc_env::AccessToTcEnv for $ty {
            fn tc_env(&self) -> &$crate::new::environment::tc_env::TcEnv {
                self.tc_env
            }
        }

        impl hash_tir::new::environment::env::AccessToEnv for $ty {
            fn env(&self) -> &hash_tir::new::environment::env::Env {
                self.tc_env().env()
            }
        }

        impl hash_intrinsics::primitives::AccessToPrimitives for $ty {
            fn primitives(&self) -> &hash_intrinsics::primitives::DefinedPrimitives {
                self.tc_env().primitives()
            }
        }

        impl hash_intrinsics::intrinsics::AccessToIntrinsics for $ty {
            fn intrinsics(&self) -> &hash_intrinsics::intrinsics::DefinedIntrinsics {
                self.tc_env().intrinsics()
            }
        }

        impl hash_reporting::diagnostic::AccessToDiagnostics for $ty {
            type Error = $crate::new::diagnostics::error::SemanticError;
            type Warning = $crate::new::diagnostics::warning::SemanticWarning;
            type Diagnostics =
                hash_reporting::diagnostic::ImmutableDiagnostics<Self::Error, Self::Warning>;

            fn diagnostics(
                &self,
            ) -> &hash_reporting::diagnostic::ImmutableDiagnostics<Self::Error, Self::Warning> {
                $crate::new::environment::tc_env::AccessToTcEnv::diagnostics(self.tc_env())
            }
        }

        impl hash_typecheck::AccessToTypechecking for $ty {
            fn proof_state(&self) -> &std::cell::RefCell<hash_typecheck::elaboration::ProofState> {
                self.tc_env().proof_state
            }

            fn convert_tc_error(&self, error: hash_typecheck::errors::TcError) -> Self::Error {
                error.into()
            }
        }
    };
}
