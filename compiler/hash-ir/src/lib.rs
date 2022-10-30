//! Hash Compiler Intermediate Representation (IR) crate.
#![allow(clippy::too_many_arguments)]

use hash_utils::{
    new_store_key,
    store::{DefaultStore, Store},
};
use ir::{Body, RValue};

pub mod ir;
pub mod visitor;
pub mod write;

new_store_key!(pub RValueId);

/// Stores all the used [RValue]s.
///
/// [Rvalue]s are accessed by an ID, of type [RValueId].
#[derive(Debug, Default)]
pub struct RValueStore {
    data: DefaultStore<RValueId, RValue>,
}

impl Store<RValueId, RValue> for RValueStore {
    fn internal_data(&self) -> &std::cell::RefCell<Vec<RValue>> {
        self.data.internal_data()
    }
}

/// Storage that is used by the IR builder.
pub struct IrStorage {
    /// The type storage for the IR.
    pub generated_bodies: Vec<Body>,

    /// The storage for all the [RValue]s.
    pub store: RValueStore,
}

impl IrStorage {
    pub fn new() -> Self {
        Self { generated_bodies: Vec::new(), store: RValueStore::default() }
    }

    /// Push an [RValue] on the storage.
    pub fn push_rvalue(&mut self, rvalue: RValue) -> RValueId {
        self.store.create(rvalue)
    }

    /// Extend the IR storage with the given bodies.
    pub fn add_bodies(&mut self, bodies: impl IntoIterator<Item = Body>) {
        self.generated_bodies.extend(bodies)
    }
}

impl Default for IrStorage {
    fn default() -> Self {
        Self::new()
    }
}
