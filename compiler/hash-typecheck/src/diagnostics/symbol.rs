//! Error-related data structures for errors that in regards to symbols
//! and symbols within error variants.

use std::fmt::Display;

/// An enum representing the origin of a named field access.
/// This is used to provide additional contextual information
/// when the validator fails to find a named field within
/// an enumeration or similar kind of [Term]. The error that
/// the validator generates with this value in mind is
/// [super::error::TcError::UnresolvedNameInValue].
#[derive(Debug, Clone)]
pub enum NameFieldOrigin {
    /// Enum nominal definition
    Enum,
    /// Inner variant of an enum
    EnumVariant,
    /// Impl or module block, unclear which it is but it shouldn't matter.
    Mod,
    /// Tuple parent subject
    Tuple,
}

impl Display for NameFieldOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NameFieldOrigin::Enum => write!(f, "enum"),
            NameFieldOrigin::EnumVariant => write!(f, "enum variant"),
            NameFieldOrigin::Mod => write!(f, "impl block"),
            NameFieldOrigin::Tuple => write!(f, "tuple"),
        }
    }
}
