//! Hash Compiler Intermediate Representation (IR) crate.
#![feature(
    let_chains,
    once_cell,
    associated_type_defaults,
    type_alias_impl_trait,
    decl_macro,
    box_patterns
)]

pub mod basic_blocks;
pub mod ir;
pub mod traversal;
pub mod ty;
pub mod visitor;
pub mod write;

use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
};

use hash_tir::{nominals::NominalDefId, terms::TermId};
use hash_utils::store::{SequenceStore, Store};
use ir::{Body, Local, Place, PlaceProjection, ProjectionStore};
use ty::{AdtData, AdtId, AdtStore, IrTy, IrTyId, TyListStore, TyStore};

/// Storage that is used by the lowering stage. This stores all of the
/// generated [Body]s and all of the accompanying data for the bodies.
#[derive(Default)]
pub struct IrStorage {
    /// The type storage for the IR.
    pub bodies: Vec<Body>,

    /// All of the accompanying data for the bodies, such as [`ir::RValue`]s,
    /// [`ty::IrTy`]s, etc. The bodies and the body data are stored separately
    /// so that the data store can be passed into various passes that occur
    /// on a particular [Body] and may perform transformations on the
    /// data.
    pub ctx: IrCtx,
}

impl IrStorage {
    pub fn new() -> Self {
        Self { bodies: Vec::new(), ctx: IrCtx::new() }
    }

    /// Extend the the [IrStorage] with the generated bodies.
    pub fn add_bodies(&mut self, bodies: impl IntoIterator<Item = Body>) {
        self.bodies.extend(bodies)
    }
}

/// A [TyCacheEntry] is used to store the [IrTyId] that is created from
/// a [TermId] or a [NominalDefId]. It is then used by program logic
/// to avoid re-computing the same type again by using this key to lookup
/// the [IrTyId] in the [IrCtx].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TyCacheEntry {
    /// The key is a term ID.
    Term(TermId),

    /// The key is a nominal definition ID.
    Nominal(NominalDefId),
}

impl From<TermId> for TyCacheEntry {
    fn from(term: TermId) -> Self {
        Self::Term(term)
    }
}

impl From<NominalDefId> for TyCacheEntry {
    fn from(nominal: NominalDefId) -> Self {
        Self::Nominal(nominal)
    }
}

/// The [IrCtx] is used to store all interned information that
/// IR [Body]s might use or reference. This includes IR types, place
/// projections, etc.
#[derive(Default)]
pub struct IrCtx {
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
    ty_cache: RefCell<HashMap<TyCacheEntry, IrTyId>>,
}

impl IrCtx {
    /// Create a new [BodyDataStore].
    pub fn new() -> Self {
        Self {
            projection_store: ProjectionStore::default(),
            ty_store: TyStore::new(),
            ty_list_store: TyListStore::default(),
            adt_store: AdtStore::new(),
            ty_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Get a reference to the [TyStore]
    pub fn tys(&self) -> &TyStore {
        &self.ty_store
    }

    /// Get a reference to the [IrTyId] cache.
    pub fn ty_cache(&self) -> Ref<HashMap<TyCacheEntry, IrTyId>> {
        self.ty_cache.borrow()
    }

    /// Add an entry to the type cache.
    pub fn add_ty_cache_entry(&self, term: TermId, ty: IrTyId) {
        self.ty_cache.borrow_mut().insert(term.into(), ty);
    }

    /// Add an "nominal" definition entry into the type cache.
    pub fn add_nominal_ty_cache_entry(&self, nominal: NominalDefId, ty: IrTyId) {
        self.ty_cache.borrow_mut().insert(nominal.into(), ty);
    }

    /// Get a reference to the [TyListStore]
    pub fn tls(&self) -> &TyListStore {
        &self.ty_list_store
    }

    /// Get a reference to the [AdtStore]
    pub fn adts(&self) -> &AdtStore {
        &self.adt_store
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

    /// Map an [IrTyId] by reading the [IrTy] that is associated with the
    /// [IrTyId] and then applying the provided function.
    pub fn map_ty<T>(&self, ty: IrTyId, f: impl FnOnce(&IrTy) -> T) -> T {
        self.ty_store.map_fast(ty, f)
    }

    /// Apply a function on an type assuming that it is a [`IrTy::Adt`].
    pub fn map_ty_as_adt<T>(&self, ty: IrTyId, f: impl FnOnce(&AdtData, AdtId) -> T) -> T {
        self.ty_store
            .map_fast(ty, |ty| self.adt_store.map_fast(ty.as_adt(), |adt| f(adt, ty.as_adt())))
    }

    /// Perform a map on a [AdtId] by reading the [AdtData] that is associated
    /// with the [AdtId] and then applying the provided function.
    pub fn map_adt<T>(&self, id: AdtId, map: impl FnOnce(AdtId, &AdtData) -> T) -> T {
        self.adts().map_fast(id, |data| map(id, data))
    }
}
