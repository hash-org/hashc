//! Defines various utilities that can be used on the AST. Mainly, this
//! crate defines AST printing functionalities, including the `tree` view
//! and the `pretty` printing view, in addition to the implementation of
//! the `#dump_ast` directive.
#![allow(dead_code)]

pub mod attr;
pub mod dump;
pub mod lit;
pub mod pretty;
pub mod tree;
