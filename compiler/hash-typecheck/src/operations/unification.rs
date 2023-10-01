use std::collections::HashSet;

use hash_tir::tir::SymbolId;
use hash_utils::state::{HeavyState, LightState};

/// Options for unification.
#[derive(Debug)]
pub struct UnificationOptions {
    /// Whether to substitute the unified terms in-place.
    pub modify_terms: LightState<bool>,
    /// A set of symbols which are bound by a pattern, so they should be unified
    /// with any other symbol. @@Reconsider: this is probably not necessary with
    /// some restructuring in unification.
    pub pat_binds: HeavyState<Option<HashSet<SymbolId>>>,
}

impl UnificationOptions {
    pub fn new() -> Self {
        Self { modify_terms: LightState::new(true), pat_binds: HeavyState::new(None) }
    }
}

impl Default for UnificationOptions {
    fn default() -> Self {
        Self::new()
    }
}
