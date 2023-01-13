use self::{data::DataUtils, params::ParamUtils};

pub mod common;
pub mod data;
pub mod params;

macro_rules! utils {
    ($($name:ident: $ty:ty),* $(,)?) => {
        pub trait AccessToUtils: $crate::new::environment::env::AccessToEnv {
            $(
                fn $name(&self) -> $ty {
                    <$ty>::new(self.env())
                }
            )*
        }
        impl<T: $crate::new::environment::env::AccessToEnv> AccessToUtils for T { }
    };
}

utils! {
  data_utils: DataUtils,
  param_utils: ParamUtils     ,
}
