use self::{builder::Builder, defs::CommonDefOps, infer::InferOps, mods::ModOps};

pub mod builder;
pub mod common;
pub mod defs;
pub mod infer;
pub mod mods;

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
  infer_ops: InferOps,
  common_def_ops: CommonDefOps,
}
