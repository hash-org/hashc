//! All of the defined logic and data structures for attribute management in the
//! Hash compiler.
#![feature(lazy_cell, let_chains, macro_metavar_expr)]

pub mod attr;
pub mod builtin;
pub mod checks;
pub mod diagnostics;
pub mod ty;
