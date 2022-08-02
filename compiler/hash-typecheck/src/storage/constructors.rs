//! Hash Typechecker [Constructor] store. Only used within
//! [crate::exhaustiveness].

use std::cell::RefCell;

use super::primitives::ConstructorId;
use crate::exhaustiveness::construct::Constructor;
use slotmap::SlotMap;

/// Store that maps [ConstructorId] to [Constructor]. This
/// is used within the [crate::exhaustiveness] in order to represent
/// patterns when checking for their usefulness and exhaustiveness.
#[derive(Debug, Default)]
pub struct ConstructorStore {
    /// Inner data store, wrapped in [RefCell] for interior
    /// mutability purposes.
    data: RefCell<SlotMap<ConstructorId, Constructor>>,
}

impl ConstructorStore {
    /// Create a new [ConstructorStore]
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a [Constructor] into the store.
    pub fn create(&self, object: Constructor) -> ConstructorId {
        self.data.borrow_mut().insert(object)
    }

    /// Get a [Constructor] by a specified [ConstructorId].
    pub fn get(&self, id: ConstructorId) -> Constructor {
        self.data.borrow().get(id).unwrap().clone()
    }

    /// Apply an update to an inner stored element within the store.
    ///
    /// **Safety**: This method expects that the `updater` closure only
    /// applies an operation on the item itself, and calls on exterior
    /// functions.
    pub fn update_unsafe(&self, id: ConstructorId, update: impl FnOnce(&mut Constructor)) {
        let mut store = self.data.borrow_mut();
        let data = store.get_mut(id).unwrap();

        update(data);
    }

    /// Map an inner [Constructor] to some other type by providing a `mapper`
    /// closure.
    ///
    /// **Safety**: This method expects that the `mapper` closure only
    /// applies an operation on the item itself, and calls on exterior
    /// functions.
    pub fn map_unsafe<U>(&self, id: ConstructorId, mapper: impl FnOnce(&Constructor) -> U) -> U {
        let store = self.data.borrow();
        let data = store.get(id).unwrap();
        mapper(data)
    }
}
