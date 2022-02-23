//! Hash compiler virtual machine crate.
//!
//! All rights reserved 2021 (c) The Hash Language authors
#![allow(dead_code)]
use std::iter;

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
        todo!()
    }
}
