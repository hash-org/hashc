//! Definition of a map that stores [Params] which can be accessed throughout
//! the typechecker in order to get the actual [Params] structure from a
//! [ParamsId].
use super::primitives::{Params, ParamsId};
use slotmap::SlotMap;

/// [Params] are accessed by an ID.
#[derive(Debug, Default)]
pub struct ParamsStore {
    data: SlotMap<ParamsId, Params>,
}

impl ParamsStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a [Params], returning its assigned [ParamsId].
    pub fn create(&mut self, ty: Params) -> ParamsId {
        self.data.insert(ty)
    }

    /// Get a [Params] by [ParamsId].
    pub fn get(&self, params_id: ParamsId) -> &Params {
        self.data.get(params_id).unwrap()
    }

    /// Get a [Params] by [ParamsId], mutably.
    pub fn get_mut(&mut self, params_id: ParamsId) -> &mut Params {
        self.data.get_mut(params_id).unwrap()
    }
}
