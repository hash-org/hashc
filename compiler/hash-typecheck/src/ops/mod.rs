//! Contains implementations of the main operations that the typechecker should be able to perform.
//!
//! Code from this module is to be used while traversing and typing the AST, in order to unify
//! types and ensure correctness.
pub mod building;
pub mod reader;
pub mod scope;
pub mod unify;
