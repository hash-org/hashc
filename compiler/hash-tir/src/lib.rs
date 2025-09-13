//! The TIR is the Typed Intermediate Representation.
//!
//! It is the next tree structure that represents the program after the AST.
//! It is used to perform semantic analysis and type checking. After this
//! stage, the TIR is lowered into the IR, which continues on down the
//! pipeline.
#![feature(decl_macro, trait_alias, never_type, unwrap_infallible, macro_metavar_expr)]
#![recursion_limit = "128"]

pub mod atom_info;
pub mod building;
pub mod context;
pub mod dump;
pub mod intrinsics;
pub mod stack;
pub mod stores;
pub mod sub;
pub mod tir;
pub mod visitor;
