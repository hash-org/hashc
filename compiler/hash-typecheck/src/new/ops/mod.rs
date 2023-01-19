//! Contains various TC-related operations, which form the core of the
//! typechecker.
use self::{
    bootstrap::BootstrapOps, context::ContextOps, elaboration::ElabOps, infer::InferOps,
    normalise::NormalisationOps, substitutions::SubstituteOps, unify::UnifyOps,
};

pub mod bootstrap;
pub mod common;
pub mod context;
pub mod elaboration;
pub mod infer;
pub mod normalise;
pub mod substitutions;
pub mod unify;

macro_rules! ops {
    ($($name:ident: $ty:ty),* $(,)? $(; $($extra:item)*)?) => {
        /// A trait that defines typechecking operations, which operate on [`TcEnv`].
        pub trait AccessToOps: $crate::new::environment::tc_env::AccessToTcEnv {
            $(
                fn $name(&self) -> $ty {
                    <$ty>::new(self.tc_env())
                }
            )*
            $(
                $(
                    $extra
                )*
            )?
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
  substitute_ops: SubstituteOps,
  elab_ops: ElabOps;
}
