//! Provides generic data structures to store values by generated keys in an
//! efficient way, with interior mutability.

pub mod base;
pub mod partial;
pub mod sequence;
pub mod statics;

pub use base::*;
pub use partial::*;
pub use sequence::*;
