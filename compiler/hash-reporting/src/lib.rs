//! Hash Compiler error and warning reporting module.
#![feature(decl_macro)]

pub mod diagnostic;
pub mod implementations;
pub mod macros;
mod render;
pub mod report;
pub mod reporter;

pub use hash_error_codes;
pub use unicode_normalization;
