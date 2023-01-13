// @@Docs
use self::{
    bootstrap::BootstrapOps, context::ContextOps, infer::InferOps, normalise::NormalisationOps,
    unify::UnifyOps,
};

pub mod bootstrap;
pub mod common;
pub mod context;
pub mod infer;
pub mod normalise;
pub mod unify;

macro_rules! ops {
    ($($name:ident: $ty:ty),* $(,)?) => {
        /// A trait that defines typechecking operations, which operate on [`TcEnv`].
        pub trait AccessToOps: $crate::new::environment::tc_env::AccessToTcEnv {
            $(
                fn $name(&self) -> $ty {
                    <$ty>::new(self.tc_env())
                }
            )*
        }
        impl<T: $crate::new::environment::tc_env::AccessToTcEnv> AccessToOps for T { }
    };
}

ops! {
  infer_ops: InferOps,
  unify_ops: UnifyOps,
  context_ops: ContextOps,
  bootstrap_ops: BootstrapOps,
  normalisation_ops: NormalisationOps,
}
