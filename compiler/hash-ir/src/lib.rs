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

use std::{
    cell::{Ref, RefCell, RefMut},
    sync::OnceLock,
};

use hash_source::entry_point::EntryPointState;
use hash_storage::stores;
use intrinsics::Intrinsics;
use ir::Body;
use lang_items::LangItems;
use ty::{AdtStore, InstanceId, InstanceStore, ReprTyListStore, ReprTyStore};

/// Storage that is used by the lowering stage. This stores all of the
/// generated [Body]s and all of the accompanying data for the bodies.
pub struct IrStorage {
    /// The type storage for the IR.
    pub bodies: Vec<Body>,

    /// All of the accompanying data for the bodies, such as [`ir::RValue`]s,
    /// [`ty::ReprTy`]s, etc. The bodies and the body data are stored separately
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

/// The [IrCtx] is used to store all interned information that
/// IR [Body]s might use or reference. This includes IR types, place
/// projections, etc.
#[derive(Default)]
pub struct IrCtx {
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
    tys: ReprTyStore,
    ty_list: ReprTyListStore,
    instances: InstanceStore,
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

        Self { lang_items: RefCell::new(lang_items), intrinsics: RefCell::new(intrinsics) }
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
}

/// Interface to access information about the representations and layout.
pub trait HasIrCtx {
    fn ir_ctx(&self) -> &IrCtx;
}
