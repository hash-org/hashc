use self::{
    builder::Builder, data::DataOps, defs::CommonDefOps, infer::InferOps, mods::ModOps,
    stack::StackOps, trts::TrtOps,
};

pub mod builder;
pub mod common;
pub mod data;
pub mod defs;
pub mod infer;
pub mod mods;
pub mod stack;
pub mod trts;

macro_rules! ops {
    ($($name:ident: $ty:ty),* $(,)?) => {
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
  builder: Builder,
  mod_ops: ModOps,
  trt_ops: TrtOps,
  data_ops: DataOps,
  stack_ops: StackOps,
  infer_ops: InferOps,
  common_def_ops: CommonDefOps,
}
