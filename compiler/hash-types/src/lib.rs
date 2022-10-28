//! Contains type definitions that the rest of the storage and the general
//! typechecker use.
#![feature(option_result_contains, let_chains, decl_macro)]
#![recursion_limit = "128"]

pub(crate) mod bootstrap;

pub mod arguments;
pub mod builder;
pub mod data;
pub mod defs;
pub mod fmt;
pub mod location;
pub mod mods;
pub mod nodes;
pub mod nominals;
pub mod params;
pub mod pats;
pub mod refs;
pub mod scope;
pub mod storage;
pub mod symbols;
pub mod terms;
pub mod trts;
pub mod types;
