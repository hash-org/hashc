use slotmap::SlotMap;

use super::primitives::{ModDef, ModDefId};

pub struct ModDefStore {
    data: SlotMap<ModDefId, ModDef>,
}
