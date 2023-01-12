//! Contains definitions related to intrinsics
use core::fmt;

use hash_utils::store::{DefaultPartialStore, PartialStore};

use super::{
    args::ArgsId,
    environment::env::{AccessToEnv, Env, WithEnv},
    fns::FnDefId,
    symbols::Symbol,
    terms::TermId,
};

/// Intrinsics live in a store.
///
/// Each intrinsic is essentially a function pointer that takes some arguments
#[derive(Clone, Copy)]
pub struct Intrinsic {
    pub name: Symbol,
    pub fn_def: FnDefId,
    pub call: fn(&Env, ArgsId) -> TermId,
}

/// An intrinsic identifier, which is just a symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IntrinsicId(pub Symbol);

pub type IntrinsicStore = DefaultPartialStore<IntrinsicId, Intrinsic>;

// Debug for intrinsics needs to be explicit to omit `call`, otherwise rust
// complains.
impl fmt::Debug for Intrinsic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Intrinsic").field("name", &self.name).finish()
    }
}

impl fmt::Display for WithEnv<'_, &Intrinsic> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "intrinsic {}", self.env().with(self.value.name))
    }
}

impl fmt::Display for WithEnv<'_, IntrinsicId> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.stores().intrinsic().map_fast(self.value, |intrinsic| {
            intrinsic
                .map(|i| write!(f, "{}", self.env().with(i)))
                .unwrap_or_else(|| write!(f, "{{intrinsic not found}}"))
        })
    }
}
