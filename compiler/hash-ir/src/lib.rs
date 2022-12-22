//! Hash Compiler Intermediate Representation (IR) crate.
#![allow(clippy::too_many_arguments)]
#![feature(let_chains, once_cell, associated_type_defaults)]

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
use hash_utils::store::{SequenceStore, Store};
use ir::{
    AggregateValueStore, Body, Local, Place, PlaceProjection, ProjectionStore, RValue, RValueId,
    RValueStore,
};
use ty::{AdtStore, IrTyId, TyListStore, TyStore};

/// Storage that is used by the lowering stage. This stores all of the
/// generated [Body]s and all of the accompanying data for the bodies.
#[derive(Default)]
pub struct IrStorage {
    /// The type storage for the IR.
    pub bodies: Vec<Body>,

    /// All of the accompanying data for the bodies, such as [RValue]s,
    /// [IrTy]s, etc. The bodies and the body data are stored separately
    /// so that the data store can be passed into various passes that occur
    /// on a particular [Body] and may perform transformations on the
    /// data.
    pub body_data: BodyDataStore,
}

impl IrStorage {
    pub fn new() -> Self {
        Self { bodies: Vec::new(), body_data: BodyDataStore::default() }
    }

    /// Get a reference to the [TyStore]
    pub fn tys(&self) -> &TyStore {
        self.body_data.tys()
    }

    /// Get a reference to the [TyListStore]
    pub fn tls(&self) -> &TyListStore {
        self.body_data.tls()
    }

    /// Get a reference to the [AdtStore]
    pub fn adts(&self) -> &AdtStore {
        self.body_data.adts()
    }

    /// Get a reference to the [AggregateValueStore]
    pub fn aggregates(&self) -> &AggregateValueStore {
        self.body_data.aggregates()
    }

    /// Get a reference to the [RValueStore]
    pub fn rvalues(&self) -> &RValueStore {
        self.body_data.rvalues()
    }

    /// Get a reference to the [ProjectionStore]
    pub fn projections(&self) -> &ProjectionStore {
        self.body_data.projections()
    }

    /// Get a reference to the type cache.
    pub fn ty_cache(&self) -> Ref<HashMap<TermId, IrTyId>> {
        self.body_data.ty_cache.borrow()
    }

    /// Add an entry to the type cache.
    pub fn add_ty_cache_entry(&self, term_id: TermId, ty_id: IrTyId) {
        self.body_data.ty_cache.borrow_mut().insert(term_id, ty_id);
    }

    /// Extend the the [IrStorage] with the generated bodies.
    pub fn add_bodies(&mut self, bodies: impl IntoIterator<Item = Body>) {
        self.bodies.extend(bodies)
    }
}

#[derive(Default)]
pub struct BodyDataStore {
    /// The storage for all the [RValue]s.
    rvalue_store: ir::RValueStore,

    /// Store collections of [RValue]s which are grouped
    /// together, such as [RValue::Aggregate]s.
    aggregate_rvalue_store: ir::AggregateValueStore,

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
    /// Create a new [BodyDataStore].
    pub fn new() -> Self {
        Self {
            rvalue_store: RValueStore::default(),
            aggregate_rvalue_store: AggregateValueStore::default(),
            projection_store: ProjectionStore::default(),
            ty_store: TyStore::default(),
            ty_list_store: TyListStore::default(),
            adt_store: AdtStore::default(),
            ty_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Get a reference to the [TyStore]
    pub fn tys(&self) -> &TyStore {
        &self.ty_store
    }

    /// Get a reference to the [TyListStore]
    pub fn tls(&self) -> &TyListStore {
        &self.ty_list_store
    }

    /// Get a reference to the [AdtStore]
    pub fn adts(&self) -> &AdtStore {
        &self.adt_store
    }

    /// Get a reference to the [RValueStore]
    pub fn rvalues(&self) -> &RValueStore {
        &self.rvalue_store
    }

    /// Get a reference to the [AggregateValueStore]
    pub fn aggregates(&self) -> &AggregateValueStore {
        &self.aggregate_rvalue_store
    }

    /// Get a reference to the [ProjectionStore]
    pub fn projections(&self) -> &ProjectionStore {
        &self.projection_store
    }

    /// Perform a map on a [Place] by reading all of the [PlaceProjection]s
    /// that are associated with the [Place] and then applying the provided
    /// function.
    pub fn map_place<T>(
        &self,
        place: Place,
        map: impl FnOnce(Local, &[PlaceProjection]) -> T,
    ) -> T {
        let Place { local, projections } = place;

        self.projections().map_fast(projections, |projections| map(local, projections))
    }

    /// Push an [RValue] on the storage.
    pub fn push_rvalue(&self, rvalue: RValue) -> RValueId {
        self.rvalue_store.create(rvalue)
    }
}
