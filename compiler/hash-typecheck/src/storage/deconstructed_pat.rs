//! Hash Typechecker [DeconstructedPat] store. Only used within
//! [crate::exhaustiveness].

use std::cell::RefCell;

use super::primitives::DeconstructedPatId;
use crate::exhaustiveness::deconstruct::DeconstructedPat;
use slotmap::SlotMap;

/// Store that maps [DeconstructedPatId] to [DeconstructedPat]. This
/// is used within the [crate::exhaustiveness] in order to represent
/// patterns when checking for their usefulness and exhaustiveness.
#[derive(Debug, Default)]
pub struct DeconstructedPatStore {
    /// Inner data store, wrapped in [RefCell] for interior
    /// mutability purposes.
    data: RefCell<SlotMap<DeconstructedPatId, DeconstructedPat>>,
}

impl DeconstructedPatStore {
    /// Create a new [DeconstructedPatStore]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a [DeconstructedPat] to the store.
    pub fn create(&self, object: DeconstructedPat) -> DeconstructedPatId {
        self.data.borrow_mut().insert(object)
    }

    /// Get a [DeconstructedPat] by a specified [DeconstructedPatId].
    pub fn get(&self, id: DeconstructedPatId) -> DeconstructedPat {
        self.data.borrow().get(id).unwrap().clone()
    }

    /// Apply an update to an inner stored element within the store.
    ///
    /// **Safety**: This method expects that the `updater` closure only
    /// applies an operation on the item itself, and calls on exterior
    /// functions.
    pub fn update_unsafe(
        &self,
        id: DeconstructedPatId,
        update: impl FnOnce(&mut DeconstructedPat),
    ) {
        let mut store = self.data.borrow_mut();
        let data = store.get_mut(id).unwrap();

        update(data);
    }
}
