use std::{
    cell::{Cell, OnceCell},
    collections::HashSet,
};

use hash_tir::tir::SymbolId;

/// Options for unification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnificationOptions {
    /// Whether to substitute the unified terms in-place.
    pub modify_terms: Cell<bool>,
    /// A set of symbols which are bound by a pattern, so they should be unified
    /// with any other symbol. @@Reconsider: this is probably not necessary with
    /// some restructuring in unification.
    pub pat_binds: OnceCell<HashSet<SymbolId>>,
}

impl UnificationOptions {
    pub fn new() -> Self {
        Self { modify_terms: Cell::new(true), pat_binds: OnceCell::new() }
    }
}

impl Default for UnificationOptions {
    fn default() -> Self {
        Self::new()
    }
}
