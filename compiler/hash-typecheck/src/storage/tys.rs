//! Contains structures to keep track of types and information relevant to them.
use super::primitives::{Ty, TyId};
use slotmap::SlotMap;

/// Stores all the types within a typechecking cycle.
///
/// Types are accessed by an ID, of type [TyId].
#[derive(Debug, Default)]
pub struct TyStore {
    data: SlotMap<TyId, Ty>,
}

impl TyStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a type, returning its assigned [TyId].
    pub fn create(&mut self, ty: Ty) -> TyId {
        self.data.insert(ty)
    }

    /// Get a type by [TyId].
    ///
    /// If the type is not found, this function will panic. However, this shouldn't happen because
    /// the only way to acquire a type is to use [Self::create], and types cannot be deleted.
    pub fn get(&self, ty_id: TyId) -> &Ty {
        self.data.get(ty_id).unwrap()
    }

    /// Get a type by [TyId], mutably.
    ///
    /// If the type is not found, this function will panic.
    pub fn get_mut(&mut self, ty_id: TyId) -> &mut Ty {
        self.data.get_mut(ty_id).unwrap()
    }
}
