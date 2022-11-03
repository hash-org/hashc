//! Definitions related to type and term holes.

use hash_utils::{new_store_key, store::DefaultStore};

/// The kind of the hole.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HoleKind {
    /// The hole is a type hole
    Ty,
    /// The hole is a term hole
    Term,
}

/// A hole, which represents a type or term that is not yet known.
#[derive(Debug, Clone, Copy)]
pub struct Hole {
    /// The ID of the hole.
    pub id: HoleId,
    /// Whether the hole is a type hole or a term hole
    pub kind: HoleKind,
    // @@Todo: do we need any additional data here?
}

new_store_key!(pub HoleId);
pub type HoleStore = DefaultStore<HoleId, Hole>;
