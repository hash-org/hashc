//! Contains type definitions that the rest of the storage and the general
//! typechecker use.
#![feature(let_chains, decl_macro, trait_alias)]
#![recursion_limit = "128"]

pub mod atom_info;
pub mod building;
pub mod context;
pub mod dump;
pub mod intrinsics;
pub mod nodes;
pub mod scopes;
pub mod stores;
pub mod sub;
pub mod visitor;
