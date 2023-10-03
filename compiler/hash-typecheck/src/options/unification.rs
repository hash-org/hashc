//! Structures that are used to keep track of options that can be set for
//! unification.
use std::collections::HashSet;

use hash_tir::tir::SymbolId;
use hash_utils::state::{HeavyState, LightState};

/// Options for unification.
#[derive(Debug)]
pub struct UnificationOptions {
    /// Whether to substitute the unified terms in-place (default is true).
    pub modify_terms: LightState<bool>,
    /// A set of symbols which are bound by a pattern, so they should be unified
    /// with any other symbol (default is None). @@Reconsider: this is probably
    /// not necessary with some restructuring in unification.
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
