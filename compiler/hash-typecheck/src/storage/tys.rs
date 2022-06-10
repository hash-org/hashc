//! Contains structures to keep track of types and information relevant to them.
use super::primitives::{ResolutionId, Ty, TyId};
use hash_source::location::SourceLocation;
use slotmap::SlotMap;
use std::{cell::Cell, collections::HashMap};

/// Stores all the types within a typechecking cycle.
///
/// Types are accessed by an ID, of type [TyId].
#[derive(Debug, Default)]
pub struct TyStore {
    /// Type data.
    data: SlotMap<TyId, Ty>,
    /// Keeps track of the last ID used for unresolved types.
    /// This will be incremented every time a [Ty::Unresolved] is created.
    ///
    /// @@Future: In the future, resolution IDs can be used to implement a pointer-based unknown
    /// type resolution, where substitutions correspond to mutating types rather than creating
    /// whole new ones. This could greatly improve performance.
    last_resolution_id: Cell<usize>,
}

impl TyStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a type, returning its assigned [TyId].
    pub fn create(&mut self, ty: Ty) -> TyId {
        self.data.insert(ty)
    }

    /// Get a type by [TyId].
    ///
    /// If the type is not found, this function will panic. However, this shouldn't happen because
    /// the only way to acquire a type is to use [Self::create], and types cannot be deleted.
    pub fn get(&self, ty_id: TyId) -> &Ty {
        self.data.get(ty_id).unwrap()
    }

    /// Get a type by [TyId], mutably.
    ///
    /// If the type is not found, this function will panic.
    pub fn get_mut(&mut self, ty_id: TyId) -> &mut Ty {
        self.data.get_mut(ty_id).unwrap()
    }

    /// Get a new [ResolutionId] for a new [Ty::Unresolved].
    ///
    /// This shouldn't be directly used in inference code, rather call the appropriate [TyBuilder]
    /// function.
    pub fn new_resolution_id(&self) -> ResolutionId {
        let new_id = self.last_resolution_id.get() + 1;
        self.last_resolution_id.set(new_id);
        ResolutionId(new_id)
    }
}

/// Stores the source location of types in the AST tree.
///
/// Not every type is guaranteed to have an attached location, but if it does it will be stored
/// here. Note that type locations are on the [TyId]-level, not on the [Ty]-level. So two identical
/// [Ty]s with different [TyId]s can have separate location attachments.
#[derive(Debug, Default)]
pub struct TyLocations {
    data: HashMap<TyId, SourceLocation>,
}

impl TyLocations {
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the location of the type with the given [TyId], if it exists.
    pub fn get_location(&self, id: TyId) -> Option<SourceLocation> {
        self.data.get(&id).map(|&x| x)
    }

    /// Attach a location to the type with the given [TyId].
    ///
    /// This will overwrite any previous location attachment for this specific type.
    pub fn add_location(&mut self, id: TyId, location: SourceLocation) {
        self.data.insert(id, location);
    }
}
