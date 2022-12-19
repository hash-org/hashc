//! Hash Compiler Intermediate Representation (IR) crate.
#![allow(clippy::too_many_arguments)]
#![feature(let_chains, once_cell)]

pub mod basic_blocks;
pub mod ir;
pub mod ty;
pub mod visitor;
pub mod write;

use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
};

use hash_types::terms::TermId;
use hash_utils::store::Store;
use ir::{Body, ProjectionStore, RValue, RValueId, RValueStore};
use ty::{AdtStore, IrTyId, TyListStore, TyStore};

/// Storage that is used by the IR builder.
#[derive(Default)]
pub struct IrStorage {
    /// The type storage for the IR.
    pub generated_bodies: Vec<Body>,

    pub body_data: BodyDataStore,
}

impl IrStorage {
    pub fn new() -> Self {
        Self { generated_bodies: Vec::new(), body_data: BodyDataStore::default() }
    }

    /// Get a reference to the [TyStore]
    pub fn tys(&self) -> &TyStore {
        &self.body_data.ty_store
    }

    /// Get a reference to the [TyListStore]
    pub fn tls(&self) -> &TyListStore {
        &self.body_data.ty_list_store
    }

    /// Get a reference to the [AdtStore]
    pub fn adts(&self) -> &AdtStore {
        &self.body_data.adt_store
    }

    /// Get a reference to the [RValueStore]
    pub fn rvalues(&self) -> &RValueStore {
        &self.body_data.rvalue_store
    }

    /// Get a reference to the [ProjectionStore]
    pub fn projections(&self) -> &ProjectionStore {
        &self.body_data.projection_store
    }

    /// Get a reference to the type cache.
    pub fn ty_cache(&self) -> Ref<HashMap<TermId, IrTyId>> {
        self.body_data.ty_cache.borrow()
    }

    /// Add an entry to the type cache.
    pub fn add_ty_cache_entry(&self, term_id: TermId, ty_id: IrTyId) {
        self.body_data.ty_cache.borrow_mut().insert(term_id, ty_id);
    }

    /// Push an [RValue] on the storage.
    pub fn push_rvalue(&self, rvalue: RValue) -> RValueId {
        self.body_data.rvalue_store.create(rvalue)
    }

    /// Extend the IR storage with the given bodies.
    pub fn add_bodies(&mut self, bodies: impl IntoIterator<Item = Body>) {
        self.generated_bodies.extend(bodies)
    }
}

#[derive(Default)]
pub struct BodyDataStore {
    /// The storage for all the [RValue]s.
    rvalue_store: ir::RValueStore,

    /// This the storage for all projection collections.
    projection_store: ir::ProjectionStore,

    /// The storage for all of the used types that are within the IR.
    ty_store: ty::TyStore,

    /// Storage for grouped types, ones that appear in a parent type, i.e. a
    /// [`IrTy::Fn(...)`] type will use the `TyListStore` to store that
    /// parameter types.
    ty_list_store: ty::TyListStore,

    /// Storage that is used to store all of the created ADTs that
    /// are registered within the IR.
    adt_store: ty::AdtStore,

    /// Cache for the [IrTyId]s that are created from [TermId]s.
    ty_cache: RefCell<HashMap<TermId, IrTyId>>,
}

impl BodyDataStore {
    pub fn new() -> Self {
        Self {
            rvalue_store: RValueStore::default(),
            projection_store: ProjectionStore::default(),
            ty_store: TyStore::default(),
            ty_list_store: TyListStore::default(),
            adt_store: AdtStore::default(),
            ty_cache: RefCell::new(HashMap::new()),
        }
    }
}
