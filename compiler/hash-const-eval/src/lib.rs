//! This is the main compiler sources for constant value management. This
//! representation is used across the compiler from AST all of the way to
//! the executable construction and or VM execution.v

pub mod error;
pub mod eval;
pub mod op;
pub mod print;
pub mod utils;

// Re-export the "primitives" from the hash-target crate so that everyone can
// use.
pub use hash_repr::constant::{Const, ConstKind};
