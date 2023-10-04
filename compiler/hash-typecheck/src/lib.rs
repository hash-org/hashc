//! The Hash typechecker crate.
//!
//! This crate implements the typechecking for the Hash language.
//!
//! Typechecking occurs on the level of the TIR. Typechecking operations for
//! each TIR node can be found in the `operations` module, while general TC
//! traits can be found in `traits`. The `utilities` module includes various
//! other functionality to deal with things such as entry points, purity checks,
//! exhaustiveness, compile-time evaluation, etc. The TC error definitions and
//! reporting are in the `errors` module. The `env` module contains a trait
//! that defines all the required items for the typechecker to work, provided by
//! the greater compiler context.

#![feature(control_flow_enum, let_chains)]

pub mod diagnostics;
pub mod env;
pub mod operations;
pub mod options;
pub mod tc;
pub mod traits;
pub mod utils;
