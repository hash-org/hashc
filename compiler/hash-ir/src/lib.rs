//! Hash Compiler Intermediate Representation (IR) crate.
#![feature(
    let_chains,
    associated_type_defaults,
    type_alias_impl_trait,
    decl_macro,
    box_patterns,
    variant_count,
    const_option
)]

pub mod basic_blocks;
pub mod cast;
pub mod constant;
pub mod intrinsics;
pub mod ir;
pub mod lang_items;
pub mod traversal;
pub mod ty;
pub mod visitor;

use std::{
    cell::{Ref, RefCell, RefMut},
    sync::OnceLock,
};

use constant::Allocations;
use hash_source::entry_point::EntryPointState;
use hash_storage::{store::SequenceStoreKey, stores};
use hash_tir::{
    intrinsics::definitions::Intrinsic as TirIntrinsic,
    tir::{
        data::{DataDefId, DataTy},
        terms::{fns::FnDefId, TyId},
    },
};
use hash_utils::fxhash::FxHashMap;
use intrinsics::Intrinsics;
use ir::{Body, ProjectionStore};
use lang_items::LangItems;
use ty::{AdtStore, InstanceId, InstanceStore, IrTyId, IrTyListStore, IrTyStore};

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

    /// An intrinsic that was lowered into a function type instance.
    Intrinsic(TirIntrinsic),
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

impl From<TirIntrinsic> for TyCacheEntry {
    fn from(intrinsic: TirIntrinsic) -> Self {
        Self::Intrinsic(intrinsic)
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
    instances: InstanceStore,
    projections: ProjectionStore,
    allocations: Allocations
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
            lang_items: RefCell::new(lang_items),
            intrinsics: RefCell::new(intrinsics),
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

    /// Get a reference to the semantic types conversion cache.
    pub fn ty_cache(&self) -> &TyCache {
        &self.ty_cache
    }
}
