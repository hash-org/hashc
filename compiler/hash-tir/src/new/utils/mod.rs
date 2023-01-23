//! Utility functions for working with TC primitives.
use self::{
    context::ContextUtils, data::DataUtils, defs::DefUtils, fns::FnUtils, mods::ModUtils,
    params::ParamUtils, stack::StackUtils, traversing::TraversingUtils, tuples::TupleUtils,
};

pub mod common;
pub mod context;
pub mod data;
pub mod defs;
pub mod fns;
pub mod mods;
pub mod params;
pub mod stack;
pub mod traversing;
pub mod tuples;

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
  def_utils: DefUtils,
  param_utils: ParamUtils     ,
  fn_utils: FnUtils,
  mod_utils: ModUtils,
  stack_utils: StackUtils,
  tuple_utils: TupleUtils,
  traversing_utils: TraversingUtils,
  context_utils: ContextUtils,
}
