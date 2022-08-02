//! Hash Typechecker pattern arena in order to store
//! [crate::exhaustiveness::deconstruct::DeconstructedPat] objects when
//! performing exhaustiveness checks.

use crate::exhaustiveness::structures::DeconstructedPat;
use slotmap::SlotMap;

use super::primitives::DeconstructedPatId;

/// Stores nominal type definitions, indexed by [NominalDefId]s.
#[derive(Debug, Default)]
pub struct DeconstructedPatStore {
    data: SlotMap<DeconstructedPatId, DeconstructedPat>,
}

impl DeconstructedPatStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn create(&mut self, object: DeconstructedPat) -> DeconstructedPatId {
        self.data.insert(object)
    }

    pub fn get(&self, id: DeconstructedPatId) -> &DeconstructedPat {
        self.data.get(id).unwrap()
    }

    pub fn get_mut(&mut self, id: DeconstructedPatId) -> &mut DeconstructedPat {
        self.data.get_mut(id).unwrap()
    }
}
