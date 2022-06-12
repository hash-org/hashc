use super::primitives::{Kind, KindId, ResolutionId};
use hash_source::location::SourceLocation;
use slotmap::{SecondaryMap, SlotMap};
use std::{cell::Cell, collections::HashMap};

/// Stores all the kinds within a typechecking cycle.
///
/// Kinds are accessed by an ID, of type [KindId].
#[derive(Debug, Default)]
pub struct KindStore {
    /// Type data.
    data: SlotMap<KindId, Kind>,
    /// Keeps track of the last ID used for unresolved kinds.
    /// This will be incremented every time a [Kind::Unresolved] is created.
    ///
    /// @@Future: In the future, resolution IDs can be used to implement a pointer-based unknown
    /// type resolution, where substitutions correspond to mutating kinds rather than creating
    /// whole new ones. This could greatly improve performance.
    last_resolution_id: Cell<usize>,
    // /// Bound data of unresolved variables
    // unresolved_bound_data: HashMap<ResolutionId, KindId>,
}

impl KindStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a kind, returning its assigned [KindId].
    pub fn create(&mut self, kind: Kind) -> KindId {
        self.data.insert(kind)
    }

    /// Get a kind by [KindId].
    ///
    /// If the kind is not found, this function will panic. However, this shouldn't happen because
    /// the only way to acquire a kind is to use [Self::create], and kinds cannot be deleted.
    pub fn get(&self, kind_id: KindId) -> &Kind {
        self.data.get(kind_id).unwrap()
    }

    /// Get a kind by [KindId], mutably.
    ///
    /// If the kind is not found, this function will panic.
    pub fn get_mut(&mut self, kind_id: KindId) -> &mut Kind {
        self.data.get_mut(kind_id).unwrap()
    }

    /// Get a new [ResolutionId] for a new [Kind::Unresolved].
    ///
    /// This shouldn't be directly used in inference code, rather call the appropriate [KindBuilder]
    /// function.
    pub fn new_resolution_id(&self) -> ResolutionId {
        let new_id = self.last_resolution_id.get() + 1;
        self.last_resolution_id.set(new_id);
        ResolutionId(new_id)
    }

    // @@TODO: reintroduce bounds for unresolved variables
    ///// Get the bound of the unresolved variable with the given [ResolutionId], if any.
    //pub fn get_bound_of_unresolved(&self, resolution_id: ResolutionId) -> Option<KindId> {
    //    self.unresolved_bound_data.get(&resolution_id).map(|&x| x)
    //}

    ///// Set the bound of the unresolved variable with the given [ResolutionId], if any.
    //pub fn set_bound_of_unresolved(&self, resolution_id: ResolutionId, bound: KindId) {
    //    self.unresolved_bound_data.insert(resolution_id, bound);
    //}
}

/// Stores the source location of kinds in the AST tree.
///
/// Not every kind is guaranteed to have an attached location, but if it does it will be stored
/// here. Note that kind locations are on the [KindId]-level, not on the [Kind]-level. So two
/// identical [Kind]s with different [KindId]s can have separate location attachments.
#[derive(Debug, Default)]
pub struct KindLocations {
    data: SecondaryMap<KindId, SourceLocation>,
}

impl KindLocations {
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the location of the kind with the given [KindId], if it exists.
    pub fn get_location(&self, id: KindId) -> Option<SourceLocation> {
        self.data.get(id).map(|&x| x)
    }

    /// Attach a location to the kind with the given [KindId].
    ///
    /// This will overwrite any previous location attachment for this specific kind.
    pub fn add_location(&mut self, id: KindId, location: SourceLocation) {
        self.data.insert(id, location);
    }
}
