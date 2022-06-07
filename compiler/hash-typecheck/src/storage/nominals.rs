use slotmap::SlotMap;

use super::primitives::{NominalDef, NominalDefId};

pub struct NominalDefStore {
    data: SlotMap<NominalDefId, NominalDef>,
}
