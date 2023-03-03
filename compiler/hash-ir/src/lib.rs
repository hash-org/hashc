//! Hash Compiler Intermediate Representation (IR) crate.
#![feature(
    let_chains,
    once_cell,
    associated_type_defaults,
    type_alias_impl_trait,
    decl_macro,
    box_patterns,
    variant_count
)]

pub mod basic_blocks;
pub mod intrinsics;
pub mod ir;
pub mod traversal;
pub mod ty;
pub mod visitor;
pub mod write;

use std::cell::RefCell;

use hash_source::entry_point::EntryPointState;
use hash_tir::{
    data::{DataDefId, DataTy},
    tys::TyId,
};
use hash_utils::store::{FxHashMap, SequenceStore, SequenceStoreKey, Store};
use intrinsics::Intrinsics;
use ir::{Body, Local, Place, PlaceProjection, ProjectionStore};
use ty::{
    AdtData, AdtId, AdtStore, Instance, InstanceId, InstanceStore, IrTy, IrTyId, TyListStore,
    TyStore,
};

/// Storage that is used by the lowering stage. This stores all of the
/// generated [Body]s and all of the accompanying data for the bodies.
pub struct IrStorage {
    /// The type storage for the IR.
    pub bodies: Vec<Body>,

    /// All of the accompanying data for the bodies, such as [`ir::RValue`]s,
    /// [`ty::IrTy`]s, etc. The bodies and the body data are stored separately
    /// so that the data store can be passed into various passes that occur
    /// on a particular [Body] and may perform transformations on the
    /// data.
    pub ctx: IrCtx,

    /// Holds information about the program entry point.
    pub entry_point: EntryPointState<InstanceId>,
}

impl Default for IrStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl IrStorage {
    pub fn new() -> Self {
        Self { bodies: Vec::new(), ctx: IrCtx::new(), entry_point: EntryPointState::new() }
    }

    /// Extend the the [IrStorage] with the generated bodies.
    pub fn add_bodies(&mut self, bodies: impl IntoIterator<Item = Body>) {
        self.bodies.extend(bodies)
    }
}

/// A [SemanticCacheEntry] is used to store the [IrTyId] that is created from
/// a [TyId] or a [DataDefId]. It is then used by program logic
/// to avoid re-computing the same type again by using this key to lookup
/// the [IrTyId] in the [IrCtx].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TyCacheEntry {
    /// The key is a type ID.
    Ty(TyId),

    /// The key is a data definition which includes the data def and the
    /// type arguments to the data definition.
    Data(DataTy),

    /// This is used as a key to lookup the type of a data definition that has
    /// no specified arguments. This means that the `args` component of [DataTy]
    /// must be of length zero. This meant as an optimisation to avoid
    /// re-creating data types that have no arguments whilst having
    /// different IDs for the arguments.
    ///
    /// This is safe to do since if no arguments are supplied to the data
    /// definition, this means that they are either all known and resolved
    /// (as in defaults) or that the data type has no type arguments at all.
    MonoData(DataDefId),
}

impl From<TyId> for TyCacheEntry {
    fn from(ty: TyId) -> Self {
        Self::Ty(ty)
    }
}

impl From<DataTy> for TyCacheEntry {
    fn from(data: DataTy) -> Self {
        if data.args.len() == 0 {
            Self::MonoData(data.data_def)
        } else {
            Self::Data(data)
        }
    }
}

/// The type cache is used to store all of the [IrTyId]s that are created
/// from [TyId]s or [DataTy]s. This is used to avoid re-computing the
/// same type again.
pub type TyCache = RefCell<FxHashMap<TyCacheEntry, IrTyId>>;

/// The [IrCtx] is used to store all interned information that
/// IR [Body]s might use or reference. This includes IR types, place
/// projections, etc.
#[derive(Default)]
pub struct IrCtx {
    /// This the storage for all projection collections.
    projection_store: ir::ProjectionStore,

    /// The storage for all of the used types that are within the IR.
    ty_store: ty::TyStore,

    /// Storage that is used to store all of the created ADTs that
    /// are registered within the IR.
    adt_store: ty::AdtStore,

    /// All of the function instances that have been created by the
    /// lowering stage.
    instances: ty::InstanceStore,

    /// Cache for the [IrTyId]s that are created from [TyId]s.
    semantic_cache: TyCache,

    /// A map of all "language" intrinsics that might need to be
    /// generated during the lowering process.
    intrinsics: Intrinsics,
}

impl IrCtx {
    /// Create a new [IrCtx].
    pub fn new() -> Self {
        let ty_store = TyStore::new();
        let instances = InstanceStore::new();
        let intrinsics = Intrinsics::new(&ty_store, &instances);

        Self {
            projection_store: ProjectionStore::default(),
            intrinsics,
            ty_store,
            instances,
            adt_store: AdtStore::new(),
            semantic_cache: RefCell::new(FxHashMap::default()),
        }
    }

    /// Get a reference to the [Intrinsics] map.
    pub fn intrinsics(&self) -> &Intrinsics {
        &self.intrinsics
    }

    /// Get a reference to the [TyStore].
    pub fn tys(&self) -> &TyStore {
        &self.ty_store
    }

    /// Get a reference to the semantic types conversion cache.
    pub fn semantic_cache(&self) -> &TyCache {
        &self.semantic_cache
    }

    /// Get a reference to the [TyListStore]
    pub fn tls(&self) -> &TyListStore {
        &self.ty_store.tls
    }

    /// Get a reference to the [AdtStore]
    pub fn adts(&self) -> &AdtStore {
        &self.adt_store
    }

    /// Get a reference to the instance store.
    pub fn instances(&self) -> &InstanceStore {
        &self.instances
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
    ///
    /// N.B. This function should not create any new [IrTy]s during the
    /// function operation.
    pub fn map_ty<T>(&self, ty: IrTyId, f: impl FnOnce(&IrTy) -> T) -> T {
        self.ty_store.map_fast(ty, f)
    }

    /// Map an [InstanceId] by reading the [Instance] that is associated with
    /// the [InstanceId] and then applying the provided function.
    ///
    /// N.B. This function should not create any new [Instance]s during the
    /// function operation.
    pub fn map_instance<T>(&self, id: InstanceId, f: impl FnOnce(&Instance) -> T) -> T {
        self.instances().map_fast(id, f)
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
