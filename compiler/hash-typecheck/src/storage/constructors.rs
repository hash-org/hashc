//! Hash Typechecker [DeconstructedCtor] store. Only used within
//! [crate::exhaustiveness].

use std::cell::RefCell;

use super::primitives::ConstructorId;
use crate::exhaustiveness::construct::DeconstructedCtor;
use slotmap::SlotMap;

/// Store that maps [ConstructorId] to [DeconstructedCtor]. This
/// is used within the [crate::exhaustiveness] in order to represent
/// patterns when checking for their usefulness and exhaustiveness.
#[derive(Debug, Default)]
pub struct DeconstructedCtorStore {
    /// Inner data store, wrapped in [RefCell] for interior
    /// mutability purposes.
    data: RefCell<SlotMap<ConstructorId, DeconstructedCtor>>,
}

impl DeconstructedCtorStore {
    /// Create a new [DeconstructedCtorStore]
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a [DeconstructedCtor] into the store.
    pub fn create(&self, object: DeconstructedCtor) -> ConstructorId {
        self.data.borrow_mut().insert(object)
    }

    /// Get a [DeconstructedCtor] by a specified [ConstructorId].
    pub fn get(&self, id: ConstructorId) -> DeconstructedCtor {
        *self.data.borrow().get(id).unwrap()
    }

    /// Apply an update to an inner stored element within the store.
    ///
    /// **Safety**: This method expects that the `updater` closure only
    /// applies an operation on the item itself, and calls on exterior
    /// functions.
    pub fn update_unsafe(&self, id: ConstructorId, update: impl FnOnce(&mut DeconstructedCtor)) {
        let mut store = self.data.borrow_mut();
        let data = store.get_mut(id).unwrap();

        update(data);
    }

    /// Map an inner [DeconstructedCtor] to some other type by providing a
    /// `mapper` closure.
    ///
    /// **Safety**: This method expects that the `mapper` closure only
    /// applies an operation on the item itself, and calls on exterior
    /// functions.
    pub fn map_unsafe<U>(
        &self,
        id: ConstructorId,
        mapper: impl FnOnce(&DeconstructedCtor) -> U,
    ) -> U {
        let store = self.data.borrow();
        let data = store.get(id).unwrap();
        mapper(data)
    }
}
