//! Hash compiler general utilities
#![feature(
    array_windows,
    cell_update,
    cfg_match,
    decl_macro,
    impl_trait_in_assoc_type,
    panic_info_message,
    type_alias_impl_trait
)]

pub mod assert;
pub mod counter;
pub mod crash;
pub mod graph;
pub mod highlight;
pub mod logging;
pub mod path;
pub mod printing;
pub mod profiling;
pub mod range_map;
pub mod scoping;
pub mod stack;
pub mod state;
pub mod temp_writer;
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
pub use num_bigint;
pub use num_traits;
pub use parking_lot;
pub use rayon;
pub use smallvec;
pub use thin_vec;
