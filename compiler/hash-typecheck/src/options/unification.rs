//! Structures that are used to keep track of options that can be set for
//! unification.

use hash_utils::state::LightState;

/// Options for unification.
#[derive(Debug)]
pub struct UnificationOptions {
    /// Whether to substitute the unified terms in-place (default is true).
    pub modify_terms: LightState<bool>,
}

impl UnificationOptions {
    pub fn new() -> Self {
        Self { modify_terms: LightState::new(true) }
    }
}

impl Default for UnificationOptions {
    fn default() -> Self {
        Self::new()
    }
}
