// @@Docs
use std::{marker::PhantomData, sync::OnceLock};

use hash_utils::store::{SequenceStore, SequenceStoreInternalData, SequenceStoreKey};
use parking_lot::RwLock;

use super::super::{
    args::{ArgsStore, PatArgsStore},
    data::{CtorDefsStore, DataDefStore},
    fns::FnDefStore,
    locations::LocationStore,
    mods::{ModDefStore, ModMembersStore},
    params::ParamsStore,
    pats::{PatListStore, PatStore},
    scopes::StackStore,
    symbols::SymbolStore,
    terms::{TermListStore, TermStore},
    tys::TyStore,
};
use crate::{
    ast_info::AstInfo, atom_info::AtomInfoStore, control::MatchCasesStore,
    directives::AppliedDirectivesStore,
};

/// This macro creates the `Stores` struct, as well as accompanying creation and
/// access methods, for the given sequence of stores.
macro_rules! stores {
  ($($name:ident: $ty:ty),* $(,)?) => {
    #[derive(Debug)]
    pub struct Stores {
        $($name: $ty),*
    }

    impl Stores {
        pub fn new() -> Self {
            Self {
                $($name: <$ty>::new()),*
            }
        }

        $(
            pub fn $name(&self) -> & $ty {
                &self.$name
            }
        )*
    }

    impl Default for Stores {
        fn default() -> Self {
            Self::new()
        }
    }
  }
}

// All the stores that contain definitions for the typechecker.
stores! {
    args: ArgsStore,
    ctor_defs: CtorDefsStore,
    data_def: DataDefStore,
    fn_def: FnDefStore,
    location: LocationStore,
    mod_def: ModDefStore,
    mod_members: ModMembersStore,
    params: ParamsStore,
    pat: PatStore,
    pat_args: PatArgsStore,
    pat_list: PatListStore,
    stack: StackStore,
    symbol: SymbolStore,
    term: TermStore,
    term_list: TermListStore,
    ty: TyStore,
    match_cases: MatchCasesStore,
    atom_info: AtomInfoStore,
    ast_info: AstInfo,
    directives: AppliedDirectivesStore,
}

/// The global `Stores` instance.
static STORES: OnceLock<Stores> = OnceLock::new();

/// Access the global `Stores` instance.
pub fn global_stores() -> &'static Stores {
    STORES.get_or_init(Stores::new)
}

/// A trait for a store ID which can be used to access a store in `STORES`.
pub trait StoreId: Sized + Copy {
    type Value;
    type ValueRef: ?Sized;

    /// Get the value associated with this ID.
    fn value(self) -> Self::Value;

    /// Map the value associated with this ID to a new value.
    fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R;

    /// Modify the value associated with this ID.
    fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R;

    /// Set the value associated with this ID.
    fn set(self, value: Self::Value);
}

/// A trait for a sequence store ID which can be used to access a store in
/// `STORES`.
pub trait SequenceStoreValue: Sized {
    type Id: StoreId;
    type ElementId: StoreId;

    /// Create a new empty value in the store.
    fn empty_seq() -> Self::Id;

    /// Create a new value in the store from the given iterator of functions.
    fn seq<F: FnOnce(Self::ElementId) -> Self, I: IntoIterator<Item = F>>(iter: I) -> Self::Id
    where
        I::IntoIter: ExactSizeIterator;
}

/// A trait for a store ID containing single items which can be used to access a
/// store in `STORES`.
pub trait SingleStoreValue: Sized {
    type Id: StoreId;

    /// Create a new value in the store from the given function.
    fn create(self) -> Self::Id {
        Self::create_with(|_| self)
    }

    /// Create a new value in the store from the given function.
    fn create_with<F: FnOnce(Self::Id) -> Self>(value: F) -> Self::Id;
}

#[derive(Debug)]
pub struct DefaultIndirectSequenceStore<K, V> {
    data: SequenceStoreInternalData<V>,
    _phantom: PhantomData<K>,
}

impl<K, V> Default for DefaultIndirectSequenceStore<K, V> {
    fn default() -> Self {
        Self { data: RwLock::new(Vec::new()), _phantom: PhantomData }
    }
}

impl<K, V> DefaultIndirectSequenceStore<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: SequenceStoreKey<ElementKey = V>, V: Clone> SequenceStore<K, V>
    for DefaultIndirectSequenceStore<K, V>
{
    fn internal_data(&self) -> &SequenceStoreInternalData<V> {
        &self.data
    }
}

/// Automatically implement `StoreId` and `SequenceStoreId` for a sequence store
/// ID type.
#[macro_export]
macro_rules! tir_sequence_store_indirect {
    (store = $store_vis:vis $store:ident, id = $id_vis:vis $id:ident[$el_id:ident], store_name = $store_name:ident) => {
        $store_vis type $store = $crate::environment::stores::DefaultIndirectSequenceStore<$id, $el_id>;
        hash_utils::new_sequence_store_key_indirect!($id_vis $id, $el_id);

        impl $crate::environment::stores::StoreId for $id {
            type Value = Vec<$el_id>;
            type ValueRef = [$el_id];

            fn value(self) -> Self::Value {
                $crate::environment::stores::global_stores().$store_name().get_vec(self)
            }

            fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R {
                $crate::environment::stores::global_stores().$store_name().map_fast(self, f)
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R {
                $crate::environment::stores::global_stores().$store_name().modify_fast(self, f)
            }

            fn set(self, value: Self::Value) {
                $crate::environment::stores::global_stores()
                    .$store_name()
                    .set_from_slice_cloned(self, &value);
            }
        }

        impl std::fmt::Debug for $id {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                <Self as $crate::environment::stores::StoreId>::map(*self, |value| {
                    for (i, el) in value.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{:?}", el)?;
                    }
                    Ok(())
                })
            }
        }

        impl From<($id, usize)> for $el_id {
            fn from((id, index): ($id, usize)) -> Self {
                $id::from(id).map(|value| value[index].clone())
            }
        }
    };
}

/// Automatically implement `StoreId` and `SequenceStoreId` for a sequence store
/// ID type.
#[macro_export]
macro_rules! tir_sequence_store_direct {
    (store = $store_vis:vis $store:ident, id = $id_vis:vis $id:ident[$el_id:ident], value = $value:ty, store_name = $store_name:ident) => {
        $store_vis type $store = hash_utils::store::DefaultSequenceStore<$id, $value>;
        hash_utils::new_sequence_store_key_direct!($id_vis $id, $el_id);

        impl $crate::environment::stores::StoreId for $id {
            type Value = Vec<$value>;
            type ValueRef = [$value];

            fn value(self) -> Self::Value {
                $crate::environment::stores::global_stores().$store_name().get_vec(self)
            }

            fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R {
                $crate::environment::stores::global_stores().$store_name().map_fast(self, f)
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R {
                $crate::environment::stores::global_stores().$store_name().modify_fast(self, f)
            }

            fn set(self, value: Self::Value) {
                $crate::environment::stores::global_stores()
                    .$store_name()
                    .set_from_slice_cloned(self, &value);
            }
        }

        impl $crate::environment::stores::SequenceStoreValue for $value {
            type Id = $id;
            type ElementId = $el_id;

            fn empty_seq() -> Self::Id {
                $crate::environment::stores::global_stores().$store_name().create_from_slice(&[])
            }

            fn seq<F: FnOnce($el_id) -> Self, I: IntoIterator<Item = F>>(values: I) -> Self::Id
            where
                I::IntoIter: ExactSizeIterator,
            {
                $crate::environment::stores::global_stores()
                    .$store_name()
                    .create_from_iter_with(values)
            }
        }

        impl $crate::environment::stores::StoreId for $el_id {
            type Value = $value;
            type ValueRef = $value;

            fn value(self) -> Self::Value {
                use hash_utils::store::TrivialKeySequenceStore;
                $crate::environment::stores::global_stores().$store_name().get_element(self.into())
            }

            fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R {
                $crate::environment::stores::global_stores()
                    .$store_name()
                    .map_fast(self.0, |v| f(&v[self.1]))
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R {
                $crate::environment::stores::global_stores()
                    .$store_name()
                    .modify_fast(self.0, |v| f(&mut v[self.1]))
            }

            fn set(self, value: Self::Value) {
                $crate::environment::stores::global_stores()
                    .$store_name()
                    .set_at_index(self.0, self.1, value);
            }
        }

        impl std::fmt::Debug for $id {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                <Self as $crate::environment::stores::StoreId>::map(*self, |value| {
                    write!(f, "{:?}", value)
                })
            }
        }

        impl std::fmt::Debug for $el_id {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                <Self as $crate::environment::stores::StoreId>::map(*self, |value| {
                    write!(f, "{:?}", value)
                })
            }
        }
    };
}

/// Automatically implement `StoreId` and `SingleStoreId` for a single store ID
/// type.
#[macro_export]
macro_rules! tir_single_store {
    (store = $store_vis:vis $store:ident, id = $id_vis:vis $id:ident, value = $value:ty, store_name = $store_name:ident) => {
        $store_vis type $store = hash_utils::store::DefaultStore<$id, $value>;
        hash_utils::new_store_key!($id_vis $id);

        impl $crate::environment::stores::StoreId for $id {
            type Value = $value;
            type ValueRef = $value;

            fn value(self) -> Self::Value {
                use hash_utils::store::CloneStore;
                $crate::environment::stores::global_stores().$store_name().get(self)
            }

            fn map<R>(self, f: impl FnOnce(&Self::Value) -> R) -> R {
                $crate::environment::stores::global_stores().$store_name().map_fast(self, f)
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::Value) -> R) -> R {
                $crate::environment::stores::global_stores().$store_name().modify_fast(self, f)
            }

            fn set(self, value: Self::Value) {
                use hash_utils::store::CloneStore;
                $crate::environment::stores::global_stores().$store_name().set(self, value);
            }
        }

        impl $crate::environment::stores::SingleStoreValue for $value {
            type Id = $id;
            fn create_with<F: FnOnce(Self::Id) -> Self>(value: F) -> Self::Id {
                $crate::environment::stores::global_stores().$store_name().create_with(value)
            }
        }

        use $crate::environment::stores::StoreId;

        impl std::fmt::Debug for $id {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.map(|value| write!(f, "{:?}", value))
            }
        }
    };
}
