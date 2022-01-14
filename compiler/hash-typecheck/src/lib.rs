//! Hash Compiler Typecheck library file
//
// All rights reserved 2021 (c) The Hash Language authors
#![feature(map_try_insert)]
#![feature(extend_one)]
#![feature(trait_alias)]
#![feature(generic_associated_types)]
#![feature(never_type)]

pub mod error;
pub mod scope;
pub mod state;
pub mod storage;
pub mod traits;
pub mod traverse;
pub mod types;
pub mod unify;
pub mod writer;
