use hash_ast::node_map::NodeMap;
use hash_source::SourceMap;
use hash_types::new::stores::Stores;

use super::{ctx::Context, source_info::CurrentSourceInfo};
use crate::diagnostics::DiagnosticsStore;

macro_rules! tc_env {
    ($($name:ident: $ty:ty),* $(,)?) => {
        /// The typed semantic analysis environment.
        ///
        /// Contains access to stores which contain the typed semantic analysis data.
        /// Also has access to the context, which contains information about the
        /// current scope of variables and facts.
        #[derive(Debug, Copy, Clone)]
        pub struct TcEnv<'tc> {
            $(
                $name: &'tc $ty,
            )*
        }

        /// Trait to be implemented for things that want to have access to the
        /// environment.
        pub trait AccessToTcEnv {
            fn env(&self) -> &TcEnv;

            $(
                fn $name(&self) -> &$ty {
                    &self.env().$name
                }
            )*
        }

        impl<'tc> TcEnv<'tc> {
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

tc_env! {
    stores: Stores,
    context: Context,
    node_map: NodeMap,
    source_map: SourceMap,
    diagnostics_store: DiagnosticsStore,
    current_source_info: CurrentSourceInfo,
}

/// Implement [`AccessToEnv`] for some type that has a field `env: Env`.
#[macro_export]
macro_rules! impl_access_to_tc_env {
    ($x:ident<$lt:lifetime>) => {
        impl<$lt> $crate::new::data::env::AccessToTcEnv for $x<$lt> {
            fn env(&self) -> &TcEnv {
                &self.env
            }
        }
    };
}

impl<'tc> AccessToTcEnv for TcEnv<'tc> {
    fn env(&self) -> &TcEnv {
        self
    }
}
