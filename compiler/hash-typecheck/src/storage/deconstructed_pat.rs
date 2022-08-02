//! Hash Typechecker pattern arena in order to store
//! [crate::exhaustiveness::ops::deconstruct::DeconstructedPat] objects when
//! performing exhaustiveness checks.

use std::cell::RefCell;

use super::primitives::DeconstructedPatId;
use crate::exhaustiveness::deconstruct::DeconstructedPat;
use slotmap::SlotMap;

#[derive(Debug, Default)]
pub struct DeconstructedPatStore {
    data: RefCell<SlotMap<DeconstructedPatId, DeconstructedPat>>,
}

impl DeconstructedPatStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn create(&self, object: DeconstructedPat) -> DeconstructedPatId {
        self.data.borrow_mut().insert(object)
    }

    pub fn get(&self, id: DeconstructedPatId) -> DeconstructedPat {
        self.data.borrow().get(id).unwrap().clone()
    }

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
