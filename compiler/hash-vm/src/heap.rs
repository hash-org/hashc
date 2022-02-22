//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]
use std::iter;

// const HEAP_GC_MULTIPLIER: usize = 2;

/// The Heap of the Hash Virtual Machine.
#[derive(Debug)]
pub struct Heap {
    values: Vec<u8>,
}

pub struct Pointer(pub u64);

impl Heap {
    pub fn new() -> Self {
        Heap { values: vec![] }
    }

    pub fn allocate(&mut self, size: u64) -> Pointer {
        let offset = self.values.len();

        self.values
            .extend(iter::repeat(0).take(size.try_into().unwrap()));

        Pointer(offset.try_into().unwrap())
    }

    pub fn free(&self, _ptr: Pointer) {
        // it's freed now
    }

    // pub fn collect(&self) {
    //     todo!()
    // }

    // pub fn should_collect(&self) -> bool {
    //     self.values.len() >= self.max_bytes
    // }

    // /// Increase the maximum heap size by the specified constant multiplier [HEAP_GC_MULTIPLIER]
    // /// which is by default set to 2.
    // pub fn increase_max_heap_size(&mut self) {
    //     self.max_bytes *= HEAP_GC_MULTIPLIER;
    // }
}
