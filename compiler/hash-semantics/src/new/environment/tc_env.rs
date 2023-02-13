use hash_intrinsics::{
    intrinsics::{AccessToIntrinsics, DefinedIntrinsics},
    primitives::{AccessToPrimitives, DefinedPrimitives},
};
use hash_reporting::diagnostic::{AccessToDiagnostics, DiagnosticCellStore, Diagnostics};
// @@Docs
use hash_tir::{
    environment::{
        context::Context,
        env::{AccessToEnv, Env},
        stores::Stores,
    },
    mods::ModDefId,
};
use hash_typecheck::{errors::TcError, AccessToTypechecking};
use once_cell::unsync::OnceCell;

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

pub type DiagnosticsStore = DiagnosticCellStore<SemanticError, SemanticWarning>;

pub type PreludeOrUnset = OnceCell<ModDefId>;

tc_env! {
    #hide env: Env<'tc>,
    diagnostics: DiagnosticsStore,
    ast_info: AstInfo,
    prelude_or_unset: PreludeOrUnset,
    primitives_or_unset: DefinedPrimitivesOrUnset,
    intrinsics_or_unset: DefinedIntrinsicsOrUnset,
}

pub struct SemanticStorage {
    pub stores: Stores,
    pub context: Context,
    pub diagnostics: DiagnosticsStore,
    pub ast_info: AstInfo,
    pub prelude_or_unset: PreludeOrUnset,
    pub primitives_or_unset: DefinedPrimitivesOrUnset,
    pub intrinsics_or_unset: DefinedIntrinsicsOrUnset,
}

impl SemanticStorage {
    pub fn new() -> Self {
        Self {
            stores: Stores::new(),
            context: Context::new(),
            diagnostics: DiagnosticsStore::new(),
            ast_info: AstInfo::new(),
            prelude_or_unset: OnceCell::new(),
            primitives_or_unset: OnceCell::new(),
            intrinsics_or_unset: OnceCell::new(),
        }
    }
}

impl Default for SemanticStorage {
    fn default() -> Self {
        Self::new()
    }
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
    type Diagnostics = DiagnosticCellStore<SemanticError, SemanticWarning>;
    fn diagnostics(&self) -> &Self::Diagnostics {
        self.diagnostics
    }
}

impl<'tc> AccessToTypechecking for TcEnv<'tc> {
    fn convert_tc_error(&self, error: TcError) -> <Self::Diagnostics as Diagnostics>::Error {
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
    type Diagnostics = DiagnosticsStore;
    fn diagnostics(&self) -> &Self::Diagnostics {
        AccessToTcEnv::diagnostics(self)
    }
}

impl<'tc, T> AccessToTypechecking for WithTcEnv<'tc, T> {
    fn convert_tc_error(&self, error: TcError) -> <Self::Diagnostics as Diagnostics>::Error {
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

/// Convenience macro for implementing [`AccessToTcEnv`] and friends
/// for a type.
#[macro_export]
macro_rules! impl_access_to_tc_env {
    ($ty:ty) => {
        impl $crate::new::environment::tc_env::AccessToTcEnv for $ty {
            fn tc_env(&self) -> &$crate::new::environment::tc_env::TcEnv {
                self.tc_env
            }
        }

        impl hash_tir::environment::env::AccessToEnv for $ty {
            fn env(&self) -> &hash_tir::environment::env::Env {
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
            type Diagnostics = hash_reporting::diagnostic::DiagnosticCellStore<
                $crate::new::diagnostics::error::SemanticError,
                $crate::new::diagnostics::warning::SemanticWarning,
            >;

            fn diagnostics(&self) -> &Self::Diagnostics {
                $crate::new::environment::tc_env::AccessToTcEnv::diagnostics(self.tc_env())
            }
        }

        impl hash_typecheck::AccessToTypechecking for $ty {
            fn convert_tc_error(
                &self,
                error: hash_typecheck::errors::TcError,
            ) -> <Self::Diagnostics as hash_reporting::diagnostic::Diagnostics>::Error {
                error.into()
            }
        }
    };
}
