//! Definitions related to symbols and names.

use hash_source::identifier::Identifier;
use hash_utils::{new_store_key, store::DefaultStore};

/// The data carried by a symbol.
///
/// This is basically just a name identifier.
///
/// This is used to avid needing to perform alpha-conversion on terms.
pub struct SymbolData {
    pub name: Identifier,
}
new_store_key!(pub Symbol);
pub type SymbolStore = DefaultStore<Symbol, SymbolData>;
