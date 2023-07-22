//! Utility functions for working with TC primitives.
use self::{mods::ModUtils, stack::StackUtils, traversing::TraversingUtils};

pub mod common;
pub mod mods;
pub mod stack;
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
  mod_utils: ModUtils,
  stack_utils: StackUtils,
  traversing_utils: TraversingUtils,
}
