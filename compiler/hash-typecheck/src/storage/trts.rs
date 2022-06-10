use slotmap::SlotMap;
use super::primitives::{TrtDef, TrtDefId};

pub struct TrtDefStore {
    data: SlotMap<TrtDefId, TrtDef>,
}
