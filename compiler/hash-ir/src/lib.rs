//! Hash Compiler Intermediate Representation (IR) crate.
#![feature(
    let_chains,
    associated_type_defaults,
    type_alias_impl_trait,
    decl_macro,
    box_patterns,
    variant_count
)]

pub mod basic_blocks;
pub mod cast;
pub mod intrinsics;
pub mod ir;
pub mod lang_items;
pub mod traversal;
pub mod ty;
pub mod visitor;
pub mod write;

use std::{
    cell::{Ref, RefCell, RefMut},
    sync::OnceLock,
};

use hash_source::entry_point::EntryPointState;
use hash_storage::{
    store::{SequenceStore, SequenceStoreKey, Store},
    stores,
};
use hash_tir::{
    data::{DataDefId, DataTy},
    fns::FnDefId,
    tys::TyId,
};
use hash_utils::fxhash::FxHashMap;
use intrinsics::Intrinsics;
use ir::{Body, Local, Place, PlaceProjection, ProjectionStore};
use lang_items::LangItems;
use ty::{
    AdtStore, CommonIrTys, Instance, InstanceId, InstanceStore, IrTyId, IrTyListStore, IrTyStore,
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

    /// A function definition that was lowered into a function type instance.
    FnDef(FnDefId),
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

impl From<FnDefId> for TyCacheEntry {
    fn from(fn_def: FnDefId) -> Self {
        Self::FnDef(fn_def)
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

    /// Commonly used types, stored in a table.
    pub common_tys: CommonIrTys,

    /// Cache for the [IrTyId]s that are created from [TyId]s.
    ty_cache: TyCache,

    /// A map of all "language" intrinsics that might need to be
    /// generated during the lowering process.
    lang_items: RefCell<LangItems>,

    /// A map of intrinsics that will be filled ion at the code generation
    /// stage based on the selected backend for the compiler.
    intrinsics: RefCell<Intrinsics>,
}

stores!(
    IrStores;
    adts: AdtStore,
    tys: IrTyStore,
    ty_list: IrTyListStore,
    instances: InstanceStore
);

/// The global [`IrStores`] instance.
static STORES: OnceLock<IrStores> = OnceLock::new();

/// Access the global [`IrStores`] instance.
pub fn ir_stores() -> &'static IrStores {
    STORES.get_or_init(IrStores::new)
}

impl IrCtx {
    /// Create a new [IrCtx].
    pub fn new() -> Self {
        let lang_items = LangItems::new();
        let intrinsics = Intrinsics::new();

        Self {
            projection_store: ProjectionStore::default(),
            lang_items: RefCell::new(lang_items),
            intrinsics: RefCell::new(intrinsics),
            common_tys: CommonIrTys::new(),
            ty_cache: RefCell::new(FxHashMap::default()),
        }
    }

    /// Get a reference to the [Intrinsics] map.
    pub fn intrinsics(&self) -> Ref<Intrinsics> {
        self.intrinsics.borrow()
    }

    /// Get a mutable reference to the [Intrinsics] map.
    pub fn intrinsics_mut(&self) -> RefMut<Intrinsics> {
        self.intrinsics.borrow_mut()
    }

    /// Get a reference to the [LangItems] map.
    pub fn lang_items(&self) -> Ref<LangItems> {
        self.lang_items.borrow()
    }

    /// Get a mutable reference to the [LangItems] map.
    pub fn lang_items_mut(&self) -> RefMut<LangItems> {
        self.lang_items.borrow_mut()
    }

    /// Get a reference to the [IrTyStore].
    pub fn tys(&self) -> &IrTyStore {
        ir_stores().tys()
    }

    /// Get a reference to the semantic types conversion cache.
    pub fn ty_cache(&self) -> &TyCache {
        &self.ty_cache
    }

    /// Get a reference to the [TyListStore]
    pub fn tls(&self) -> &IrTyListStore {
        ir_stores().ty_list()
    }

    /// Get a reference to the [AdtStore]
    pub fn adts(&self) -> &AdtStore {
        ir_stores().adts()
    }

    /// Get a reference to the instance store.
    pub fn instances(&self) -> &InstanceStore {
        ir_stores().instances()
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

    /// Map an [InstanceId] by reading the [Instance] that is associated with
    /// the [InstanceId] and then applying the provided function.
    ///
    /// N.B. This function should not create any new [Instance]s during the
    /// function operation.
    pub fn map_instance<T>(&self, id: InstanceId, f: impl FnOnce(&Instance) -> T) -> T {
        self.instances().map_fast(id, f)
    }
}
