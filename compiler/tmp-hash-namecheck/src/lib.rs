//! This crate is responsible for performing lexical analysis on the Hash AST.
//!
//! The lexical analysis pass occurs after the AST expansion and desugaring, and
//! just before the type checking pass. Here, all names are resolved to their
//! corresponding definitions, and scopes of definitions are gathered and
//! indexed by AST node IDs.
//!
//! This pass also checks for recursive definitions, and reports an error if
//! a recursive definition is invalid.
pub mod ast;
pub mod referencing;
