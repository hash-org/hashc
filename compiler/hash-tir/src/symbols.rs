//! Definitions related to symbols and names.

use std::fmt::Display;

use hash_source::identifier::Identifier;
use hash_utils::store::{Store, StoreKey};

use crate::{environment::stores::StoreId, tir_get, tir_single_store};

/// The data carried by a symbol.
///
/// For each context, each distinct member in the context will be given a
/// different `SymbolId`. `SymbolId`s are never "shadowed" like names in a scope
/// stack might; new ones are always created for names that might shadow
/// previous names.
///
/// For example:
/// ```notrust
/// {
///     foo := 3 // -- SymbolId(72)
///     {
///         foo := 4 // -- SymbolId(73)
///     }
/// }
/// ```
///
///
/// This is used to avoid needing to perform alpha-conversion on terms when
/// performing substitutions.
#[derive(Debug, Clone, Copy)]
pub struct SymbolData {
    /// The symbol itself
    pub symbol: Symbol,
    /// A symbol might originate from an identifier name.
    ///
    /// If this is `None`, then the symbol is "internal"/generated by the
    /// compiler, and cannot be referenced by the user.
    pub name: Option<Identifier>,
}

tir_single_store!(
    store = pub SymbolStore,
    id = pub Symbol,
    value = SymbolData,
    store_name = symbol
);

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value().name {
            Some(name) => {
                f.debug_tuple("Symbol").field(&self.index).field(&format!("{}", name)).finish()
            }
            None => f.debug_tuple("Symbol").field(&self.index).finish(),
        }
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match tir_get!(*self, name) {
            Some(name) => write!(f, "{name}"),
            None => write!(f, "s{}", self.to_index()),
        }
    }
}
