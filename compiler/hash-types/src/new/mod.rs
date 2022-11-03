//! Contains definitions that are relevant to the typed semantic analysis stage
//! of the compiler (in other words, typechecking).

pub mod access;
pub mod args;
pub mod casting;
pub mod context;
pub mod control;
pub mod data;
pub mod defs;
pub mod fns;
pub mod holes;
pub mod lits;
pub mod mods;
pub mod params;
pub mod pats;
pub mod refs;
pub mod scopes;
pub mod symbols;
pub mod terms;
pub mod trts;
pub mod tuples;
pub mod tys;
pub mod unions;