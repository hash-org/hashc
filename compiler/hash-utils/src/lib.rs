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
pub mod timing;
pub mod tree_writing;

// Re-export commonly used packages
pub use arrayvec;
pub use backtrace;
pub use bitflags;
pub use fxhash;
pub use index_vec;
pub use itertools;
pub use lazy_static;
pub use log;
pub use parking_lot;
pub use smallvec;
pub use thin_vec;
