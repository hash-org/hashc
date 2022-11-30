// @@Docs
use hash_types::new::environment::env::{AccessToEnv, Env};

use crate::new::diagnostics::store::DiagnosticsStore;

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
                $name: &'tc $ty $(<$lt>)?,
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

tc_env! {
    #hide env: Env<'tc>,
    diagnostics: DiagnosticsStore,
}

/// Implement [`AccessToEnv`] for some type that has a field `env: Env`.
#[macro_export]
macro_rules! impl_access_to_tc_env {
    ($x:ident<$lt:lifetime>) => {
        impl<$lt> $crate::new::environment::tc_env::AccessToTcEnv for $x<$lt> {
            fn tc_env(&self) -> &TcEnv {
                &self.tc_env
            }
        }

        impl<$lt> hash_types::new::environment::env::AccessToEnv for $x<$lt> {
            fn env(&self) -> &hash_types::new::environment::env::Env {
                <TcEnv<'_> as hash_types::new::environment::env::AccessToEnv>::env(self.tc_env)
            }
        }
    };
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

/// A reference to [`TcEnv`] alongside a value.
///
/// This is useful for passing around a reference to the tcenv alongside
/// some value.
pub struct WithTcEnv<'tc, T> {
    env: &'tc TcEnv<'tc>,
    pub value: T,
}

impl<'tc, T: Clone> Clone for WithTcEnv<'tc, T> {
    fn clone(&self) -> Self {
        Self { env: self.env, value: self.value.clone() }
    }
}
impl<'tc, T: Copy> Copy for WithTcEnv<'tc, T> {}

impl<'tc, T> WithTcEnv<'tc, T> {
    pub fn new(env: &'tc TcEnv, value: T) -> Self {
        Self { env, value }
    }

    pub fn tc_env(&self) -> &TcEnv {
        self.env
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> WithTcEnv<'tc, U> {
        WithTcEnv { env: self.env, value: f(self.value) }
    }
}

impl<'tc> TcEnv<'tc> {
    /// Attach a value to a [`TcEnv`] reference, creating a
    /// [`WithTcEnv`] value.
    pub fn with<T>(&self, value: T) -> WithTcEnv<T> {
        WithTcEnv::new(self, value)
    }
}
