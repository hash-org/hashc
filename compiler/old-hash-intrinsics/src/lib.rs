//! This crate contains definitions of intrinsics and primitives, which are used
//! during typechecking and beyond.
//!
//! Intrinsics are functions that are opaque in the Hash code, and correspond to
//! "core" operations such as aborting, arithmetic, IO/syscalls, etc.
//!
//! Primitives are data types which are present by-default in Hash code, and
//! might have specialised (opaque) implementations, such as lists, strings,
//! maps, sets, integers, etc.

pub mod intrinsics;
pub mod utils;
