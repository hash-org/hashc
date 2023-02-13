//! Contains definitions related to intrinsics

use super::symbols::Symbol;

/// An intrinsic identifier, which is just a symbol.
///
/// Intrinsics are defined in the `hash-intrinsics` crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IntrinsicId(pub Symbol);
