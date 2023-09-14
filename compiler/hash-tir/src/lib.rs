//! The TIR is the Typed Intermediate Representation.
//!
//! It is the next tree structure that represents the program after the AST.
//! It is used to perform semantic analysis and type checking. After this
//! stage, the TIR is lowered into the IR, which continues on down the
//! pipeline.
#![feature(let_chains, decl_macro, trait_alias)]
#![recursion_limit = "128"]

pub mod atom_info;
pub mod building;
pub mod context;
pub mod dump;
pub mod intrinsics;
pub mod scopes;
pub mod stores;
pub mod sub;
pub mod tir;
pub mod visitor;
