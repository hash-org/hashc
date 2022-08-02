//! Hash Typechecker pattern arena in order to store
//! [crate::exhaustiveness::ops::construct::Constructor] objects when
//! performing exhaustiveness checks.

use std::cell::RefCell;

use super::primitives::ConstructorId;
use crate::exhaustiveness::construct::Constructor;
use slotmap::SlotMap;

#[derive(Debug, Default)]
pub struct ConstructorStore {
    data: RefCell<SlotMap<ConstructorId, Constructor>>,
}

impl ConstructorStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn create(&self, object: Constructor) -> ConstructorId {
        self.data.borrow_mut().insert(object)
    }

    pub fn get(&self, id: ConstructorId) -> Constructor {
        self.data.borrow().get(id).unwrap().clone()
    }

    pub fn update_unsafe(&self, id: ConstructorId, update: impl FnOnce(&mut Constructor)) {
        let mut store = self.data.borrow_mut();
        let data = store.get_mut(id).unwrap();

        update(data);
    }

    ///
    /// *Safety*: You cannot access
    pub fn map_unsafe<U>(&self, id: ConstructorId, mapper: impl FnOnce(&Constructor) -> U) -> U {
        let store = self.data.borrow();
        let data = store.get(id).unwrap();
        mapper(data)
    }
}
