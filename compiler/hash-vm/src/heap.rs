//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors

use hash_utils::counter;
use hashbrown::HashMap;

const HEAP_GC_MULTIPLIER: u64 = 2;

counter! {
    name: HeapId,
    counter_name: HEAP_ID_COUNTER,
    visibility: pub,
    method_visibility: pub,
}

pub struct HeapValue {}

/// The Heap of the Hash Virtual Machine.
pub struct Heap {
    allocated_bytes: u64,
    max_bytes: u64,
    values: HashMap<HeapId, HeapValue>,
}

impl Heap {
    pub fn new() -> Self {
        Heap {
            allocated_bytes: 0,
            max_bytes: 0,
            values: HashMap::default(),
        }
    }

    pub fn should_collect(&self) -> bool {
        self.allocated_bytes >= self.max_bytes
    }

    /// Increase the maximum heap size by the specified constant multiplier [HEAP_GC_MULTIPLIER]
    /// which is by default set to 2.
    pub fn increase_max_heap_size(&mut self) {
        self.max_bytes *= HEAP_GC_MULTIPLIER;
    }
}
