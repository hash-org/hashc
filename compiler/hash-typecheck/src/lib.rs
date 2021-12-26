#![feature(map_try_insert)]
#![feature(extend_one)]

//! Hash Compiler Typecheck library file
//
// All rights reserved 2021 (c) The Hash Language authors
#![feature(generic_associated_types)]

pub mod types;
// mod substitute;
pub mod writer;
pub mod traverse;
pub mod storage;
pub mod unify;
pub mod traits;
pub mod scope;
pub mod state;
