//! This is the main compiler sources for constant value management. This
//! representation is used across the compiler from AST all of the way to
//! the executable construction and or VM execution.v
#![feature(const_option)]

pub mod error;
pub mod eval;
pub mod op;

// Re-export the "primitives" from the hash-target crate so that everyone can
// use.
pub use hash_layout::constant::{Const, ConstKind, Ty};
