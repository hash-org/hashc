use hash_ast::node_map::NodeMap;
use hash_source::SourceMap;
use hash_target::Target;

use super::source_info::CurrentSourceInfo;
use crate::environment::{context::Context, stores::Stores};

macro_rules! env {
    ($($name:ident: $ty:ty),* $(,)?) => {
        /// The typed semantic analysis env.
        ///
        /// Contains access to stores which contain the typed semantic analysis data.
        /// Also has access to the context, which contains information about the
        /// current scope of variables and facts.
        #[derive(Debug, Copy, Clone)]
        pub struct Env<'tc> {
            $(
                $name: &'tc $ty,
            )*
        }

        /// Trait to be implemented for things that want to have access to the
        /// env.
        pub trait AccessToEnv {
            fn env(&self) -> &Env;

            $(
                fn $name(&self) -> &$ty {
                    &self.env().$name
                }
            )*
        }

        impl<'tc> Env<'tc> {
            pub fn new(
                $(
                    $name: &'tc $ty,
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
}

env! {
    stores: Stores,
    context: Context,
    node_map: NodeMap,
    source_map: SourceMap,
    target: Target,
    current_source_info: CurrentSourceInfo,
}

/// Implement [`AccessToEnv`] for some type that has a field `env: Env`.
#[macro_export]
macro_rules! impl_access_to_env {
    ($x:ident<$lt:lifetime>) => {
        impl<$lt> $crate::environment::env::AccessToEnv for $x<$lt> {
            fn env(&self) -> &Env {
                &self.env
            }
        }
    };
}

impl<'tc> AccessToEnv for Env<'tc> {
    fn env(&self) -> &Env {
        self
    }
}

/// A reference to [`Env`] alongside a value.
///
/// This is useful for passing around a reference to the environment alongside
/// some value.
pub struct WithEnv<'tc, T> {
    env: &'tc Env<'tc>,
    pub value: T,
}

impl<'tc, T: Clone> Clone for WithEnv<'tc, T> {
    fn clone(&self) -> Self {
        Self { env: self.env, value: self.value.clone() }
    }
}
impl<'tc, T: Copy> Copy for WithEnv<'tc, T> {}

impl<'tc, T> WithEnv<'tc, T> {
    pub fn new(env: &'tc Env, value: T) -> Self {
        Self { env, value }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> WithEnv<'tc, U> {
        WithEnv { env: self.env, value: f(self.value) }
    }
}

impl<'tc, T> AccessToEnv for WithEnv<'tc, T> {
    fn env(&self) -> &Env {
        self.env
    }
}

impl<'tc> Env<'tc> {
    /// Attach a value to a [`Env`] reference, creating a
    /// [`WithEnv`] value.
    pub fn with<T>(&self, value: T) -> WithEnv<T> {
        WithEnv::new(self, value)
    }
}
