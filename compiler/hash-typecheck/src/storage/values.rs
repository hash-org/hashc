//! Contains structures to keep track of values and information relevant to them.
use super::primitives::{Term, TermId};
use slotmap::SlotMap;

/// Stores all the values within a typechecking cycle.
///
/// Values are accessed by an ID, of value [ValueId].
#[derive(Debug, Default)]
pub struct ValueStore {
    data: SlotMap<TermId, Term>,
}

impl ValueStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a value, returning its assigned [ValueId].
    pub fn create(&mut self, ty: Term) -> TermId {
        self.data.insert(ty)
    }

    /// Get a value by [ValueId].
    ///
    /// If the value is not found, this function will panic. However, this shouldn't happen because
    /// the only way to acquire a value is to use [Self::create], and values cannot be deleted.
    pub fn get(&self, ty_id: TermId) -> &Term {
        self.data.get(ty_id).unwrap()
    }

    /// Get a value by [ValueId], mutably.
    ///
    /// If the value is not found, this function will panic.
    pub fn get_mut(&mut self, ty_id: TermId) -> &mut Term {
        self.data.get_mut(ty_id).unwrap()
    }
}
