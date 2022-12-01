// @@Docs
use self::{data::DataOps, defs::CommonDefOps, infer::InferOps, mods::ModOps, stack::StackOps};

pub mod common;
pub mod data;
pub mod defs;
pub mod infer;
pub mod mods;
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
}
