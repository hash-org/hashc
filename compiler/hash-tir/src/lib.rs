//! Contains type definitions that the rest of the storage and the general
//! typechecker use.
#![feature(option_result_contains, let_chains, decl_macro, trait_alias)]
#![recursion_limit = "128"]

pub mod access;
pub mod args;
pub mod atom_info;
pub mod casting;
pub mod control;
pub mod data;
pub mod defs;
pub mod directives;
pub mod environment;
pub mod fns;
pub mod holes;
pub mod intrinsics;
pub mod lits;
pub mod locations;
pub mod mods;
pub mod old;
pub mod params;
pub mod pats;
pub mod refs;
pub mod scopes;
pub mod sub;
pub mod symbols;
pub mod terms;
pub mod tuples;
pub mod tys;
pub mod utils;
