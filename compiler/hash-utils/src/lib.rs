//! Hash compiler general utilities
#![feature(
    type_alias_impl_trait,
    impl_trait_in_assoc_type,
    decl_macro,
    array_windows,
    panic_info_message
)]

pub mod assert;
pub mod counter;
pub mod crash;
pub mod graph;
pub mod highlight;
pub mod logging;
pub mod path;
pub mod printing;
pub mod range_map;
pub mod stack;
pub mod state;
pub mod store;
pub mod timing;
pub mod tree_writing;

// Re-export commonly used vector packages
pub use arrayvec;
pub use index_vec;
pub use itertools;
// Re-export logging utility
pub use log;
pub use smallvec;
pub use thin_vec;
