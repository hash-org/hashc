//! Defines various utilties that can be used on the AST. Mainly, this
//! crate defines AST printing functionalities, including the `tree` view
//! and the `pretty` prininging view, in addition to the implementation of
//! the `#dump_ast` directive.
#![feature(let_chains)]

pub mod attr;
pub mod dump;
pub mod lit;
pub mod pretty;
pub mod tree;
