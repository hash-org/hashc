//! The Hash typecheker.
//!
//! This brings light to the world by ensuring the correctness of the crude and dangerous Hash
//! program that is given as input to the compiler.
//!
//! @@Todo(kontheocharis): write docs about the stages of the typechecker.
pub mod error;
pub mod fmt;
pub mod infer;
pub mod ops;
pub mod storage;
