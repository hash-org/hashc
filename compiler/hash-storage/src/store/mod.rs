//! Provides generic data structures to store values by generated keys in an
//! efficient way, with interior mutability.

pub mod base;
pub use base::*;

pub mod partial;
pub mod sequence;
pub mod statics;

pub use partial::*;
pub use sequence::*;

/// This macro creates a storages struct, as well as accompanying creation and
/// access methods, for the given sequence of stores.
#[macro_export]
macro_rules! stores {
    ($store_name:ident; $($name:ident: $ty:ty),* $(,)?) => {
      #[derive(Debug)]
      pub struct $store_name {
          $($name: $ty),*
      }

      impl $store_name {
          pub fn new() -> Self {
              Self {
                  $($name: <$ty>::new()),*
              }
          }

          $(
              pub fn $name(&self) -> & $ty {
                  &self.$name
              }
          )*
      }

      impl Default for $store_name {
          fn default() -> Self {
              Self::new()
          }
      }
    }
  }
