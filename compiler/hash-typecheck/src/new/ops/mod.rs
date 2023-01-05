// @@Docs
use self::{
    context::ContextOps, data::DataOps, defs::CommonDefOps, fns::FnOps, infer::InferOps,
    mods::ModOps, params::ParamOps, stack::StackOps, tuple::TupleOps,
};

pub mod bootstrap;
pub mod common;
pub mod context;
pub mod data;
pub mod defs;
pub mod fns;
pub mod infer;
pub mod mods;
pub mod normalise;
pub mod oracle;
pub mod params;
pub mod stack;
pub mod tuple;

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
  mod_ops: ModOps,
  data_ops: DataOps,
  stack_ops: StackOps,
  infer_ops: InferOps,
  common_def_ops: CommonDefOps,
  fn_ops: FnOps,
  param_ops: ParamOps,
  context_ops: ContextOps,
  tuple_ops: TupleOps,
}
