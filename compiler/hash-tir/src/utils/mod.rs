//! Utility functions for working with TC primitives.
use self::{params::ParamUtils, traversing::TraversingUtils};

pub mod common;
pub mod params;
pub mod traversing;

macro_rules! utils {
    ($($name:ident: $ty:ty),* $(,)?) => {
        pub trait AccessToUtils: $crate::environment::env::AccessToEnv {
            $(
                fn $name(&self) -> $ty {
                    <$ty>::new(self.env())
                }
            )*
        }
        impl<T: $crate::environment::env::AccessToEnv + ?Sized> AccessToUtils for T { }
    };
}

utils! {
  param_utils: ParamUtils,
  traversing_utils: TraversingUtils,
}
