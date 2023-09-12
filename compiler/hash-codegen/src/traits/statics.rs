use hash_target::alignment::Alignment;

use super::BackendTypes;

/// A trait that gathers all of the functionality for dealing with static
/// values which need to be emitted into a backend.
pub trait StaticMethods: BackendTypes {
    /// Compute the base address of a static value.
    fn static_addr_of(&self, cv: Self::Value, align: Alignment) -> Self::Value;
}
