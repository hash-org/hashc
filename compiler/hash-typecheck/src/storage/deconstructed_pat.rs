//! Hash Typechecker pattern arena in order to store
//! [crate::exhaustiveness::deconstruct::DeconstructedPat] objects when
//! performing exhaustiveness checks.

use crate::exhaustiveness::deconstruct::DeconstructedPat;
use slotmap::SlotMap;


use super::primitives::{DeconstructedPatFieldsId};

/// Stores nominal type definitions, indexed by [NominalDefId]s.
#[derive(Debug, Default)]
pub struct DeconstructedPatStore {
    data: SlotMap<DeconstructedPatFieldsId, Vec<DeconstructedPat>>,
}

impl DeconstructedPatStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn create(&mut self, id: Vec<DeconstructedPat>) -> DeconstructedPatFieldsId {
        self.data.insert(id)
    }

    pub fn get(&self, id: DeconstructedPatFieldsId) -> &Vec<DeconstructedPat> {
        self.data.get(id).unwrap()
    }

    /// Get a nominal type definition by [NominalDefId], mutably.
    ///
    /// If the nominal type definition is not found, this function will panic.
    pub fn get_mut(&mut self, id: DeconstructedPatFieldsId) -> &mut Vec<DeconstructedPat> {
        self.data.get_mut(id).unwrap()
    }
}
