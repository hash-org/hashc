//! Contains type definitions that the rest of the storage and the general
//! typechecker use.
#![feature(option_result_contains, let_chains, decl_macro)]
#![recursion_limit = "128"]

pub(crate) mod bootstrap;

pub mod args;
pub mod builder;
pub mod fmt;
pub mod location;
pub mod mods;
pub mod new;
pub mod nodes;
pub mod nominals;
pub mod params;
pub mod pats;
pub mod scope;
pub mod storage;
pub mod terms;
pub mod trts;