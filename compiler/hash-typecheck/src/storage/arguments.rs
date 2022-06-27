//! Definition of a map that stores [Args] which can be accessed throughout
//! the typechecker in order to get the actual [Args] structure from a [ArgsId].
use super::primitives::{Args, ArgsId};
use slotmap::SlotMap;

/// [Args] are accessed by an ID.
#[derive(Debug, Default)]
pub struct ArgsStore {
    data: SlotMap<ArgsId, Args>,
}

impl ArgsStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a [Args], returning its assigned [ArgsId].
    pub fn create(&mut self, args: Args) -> ArgsId {
        self.data.insert(args)
    }

    /// Get a [Args] by [ArgsId].
    pub fn get(&self, args_id: ArgsId) -> &Args {
        self.data.get(args_id).unwrap()
    }

    /// Get a [Args] by [ArgsId], mutably.
    pub fn get_mut(&mut self, args_id: ArgsId) -> &mut Args {
        self.data.get_mut(args_id).unwrap()
    }
}
