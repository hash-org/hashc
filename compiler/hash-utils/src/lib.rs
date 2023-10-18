//! Hash compiler general utilities
#![feature(
    type_alias_impl_trait,
    impl_trait_in_assoc_type,
    decl_macro,
    array_windows,
    panic_info_message
)]

pub mod assert;
pub mod context;
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
pub use clap;
pub use crossbeam_channel;
pub use dashmap;
pub use derive_more;
pub use fnv;
pub use fxhash;
pub use index_vec;
pub use indexmap;
pub use itertools;
pub use lazy_static;
pub use log;
pub use parking_lot;
pub use rayon;
pub use smallvec;
pub use thin_vec;
