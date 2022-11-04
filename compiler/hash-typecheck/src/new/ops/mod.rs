use self::{builder::Builder, mods::ModOps, ty_ops::TyOps};

pub mod builder;
pub mod mods;
pub mod ty_ops;

macro_rules! ops {
    ($($name:ident: $ty:ty),* $(,)?) => {
        pub trait AccessToOps: $crate::new::data::env::AccessToTcEnv {
            $(
                fn $name(&self) -> $ty {
                    <$ty>::new(self.env())
                }
            )*
        }
        impl<T: $crate::new::data::env::AccessToTcEnv> AccessToOps for T { }
    };
}

ops! {
  builder: Builder,
  mod_ops: ModOps,
  ty_ops: TyOps,
}
