use slotmap::SlotMap;

use super::primitives::{Ty, TyId};

// TyStore
//
// - create: (Ty) -> TyId
// - get: (TyId) -> Ty
//
// // functions to create and get Ty::X/TyId for Ty::X

pub struct TyStore {
    data: SlotMap<TyId, Ty>,
}
