//! Hash Compiler Intermediate Representation (IR) crate.
#![allow(clippy::too_many_arguments)]

pub mod ir;
pub mod ty;
pub mod visitor;
pub mod write;

use hash_utils::store::Store;
use ir::{Body, RValue, RValueId, RValueStore};
use ty::{AdtStore, TyListStore, TyStore};

/// Storage that is used by the IR builder.
pub struct IrStorage {
    /// The type storage for the IR.
    pub generated_bodies: Vec<Body>,

    /// The storage for all the [RValue]s.
    rvalue_store: ir::RValueStore,

    /// The storage for all of the used types that are within the IR.
    ty_store: ty::TyStore,

    /// Storage for grouped types, ones that appear in a parent type, i.e. a
    /// [`IrTy::Fn(...)`] type will use the `TyListStore` to store that
    /// parameter types.
    ty_list_store: ty::TyListStore,

    /// Storage that is used to store all of the created ADTs that
    /// are registered within the IR.
    adt_store: ty::AdtStore,
}

impl IrStorage {
    pub fn new() -> Self {
        Self {
            generated_bodies: Vec::new(),
            rvalue_store: RValueStore::default(),
            ty_store: TyStore::default(),
            ty_list_store: TyListStore::default(),
            adt_store: AdtStore::default(),
        }
    }

    /// Get a reference to the [TyStore]
    pub fn ty_store(&self) -> &TyStore {
        &self.ty_store
    }

    /// Get a reference to the [TyListStore]
    pub fn ty_list_store(&self) -> &TyListStore {
        &self.ty_list_store
    }

    /// Get a reference to the [AdtStore]
    pub fn adt_store(&self) -> &AdtStore {
        &self.adt_store
    }

    /// Get a reference to the [RValueStore]
    pub fn rvalue_store(&self) -> &RValueStore {
        &self.rvalue_store
    }

    /// Push an [RValue] on the storage.
    pub fn push_rvalue(&mut self, rvalue: RValue) -> RValueId {
        self.rvalue_store.create(rvalue)
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
