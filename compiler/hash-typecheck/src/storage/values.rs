//! Contains structures to keep track of values and information relevant to them.
use super::primitives::{Value, ValueId};
use slotmap::SlotMap;

/// Stores all the values within a valuechecking cycle.
///
/// Values are accessed by an ID, of value [ValueId].
#[derive(Debug, Default)]
pub struct ValueStore {
    data: SlotMap<ValueId, Value>,
}

impl ValueStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a value, returning its assigned [ValueId].
    pub fn create(&mut self, ty: Value) -> ValueId {
        self.data.insert(ty)
    }

    /// Get a value by [ValueId].
    ///
    /// If the value is not found, this function will panic. However, this shouldn't happen because
    /// the only way to acquire a value is to use [Self::create], and values cannot be deleted.
    pub fn get(&self, ty_id: ValueId) -> &Value {
        self.data.get(ty_id).unwrap()
    }

    /// Get a value by [ValueId], mutably.
    ///
    /// If the value is not found, this function will panic.
    pub fn get_mut(&mut self, ty_id: ValueId) -> &mut Value {
        self.data.get_mut(ty_id).unwrap()
    }
}
