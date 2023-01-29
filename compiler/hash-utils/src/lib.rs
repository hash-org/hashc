//! Hash compiler general utilities
#![feature(type_alias_impl_trait, decl_macro)]

pub mod assert;
pub mod counter;
pub mod graph;
pub mod path;
pub mod printing;
pub mod stack;
pub mod state;
pub mod store;
pub mod timing;
pub mod tree_writing;

// Re-export commonly used vector packages
pub use index_vec;
pub use smallvec;
