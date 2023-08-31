//! This defines a bunch of store variants (including single and sequence)
//! which can be used as a static store.

use std::marker::PhantomData;

use parking_lot::RwLock;

use super::{SequenceStore, SequenceStoreInternalData, SequenceStoreKey};

/// A trait for a store ID which can be used to access a store in a store.
pub trait PartialStoreId: Sized + Copy {
    type Value;
    type ValueRef: ?Sized;
    type ValueBorrow;
    type ValueBorrowMut;

    /// Borrow the value associated with this ID.
    fn borrow(self) -> Option<Self::ValueBorrow>;

    /// Borrow the value associated with this ID mutably.
    fn borrow_mut(self) -> Option<Self::ValueBorrowMut>;

    /// Get the value associated with this ID.
    fn value(self) -> Option<Self::Value>;

    /// Map the value associated with this ID to a new value.
    fn map<R>(self, f: impl FnOnce(Option<&Self::ValueRef>) -> R) -> R;

    /// Modify the value associated with this ID.
    fn modify<R>(self, f: impl FnOnce(Option<&mut Self::ValueRef>) -> R) -> R;

    /// Insert or set the value associated with this ID.
    fn insert(self, value: Self::Value);

    /// Whether the value associated with this ID exists.
    fn exists(self) -> bool;
}

/// A trait for a store ID which can be used to access a store in a store.
pub trait StoreId: Sized + Copy {
    type Value;
    type ValueRef: ?Sized;
    type ValueBorrow;
    type ValueBorrowMut;

    /// Borrow the value associated with this ID.
    fn borrow(self) -> Self::ValueBorrow;

    /// Borrow the value associated with this ID mutably.
    fn borrow_mut(self) -> Self::ValueBorrowMut;

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
    type ElementId;

    /// Create a new empty value in the store.
    fn empty_seq() -> Self::Id;

    /// Create a new value in the store from the given iterator of values.
    fn seq<I: IntoIterator<Item = Self>>(iter: I) -> Self::Id
    where
        I::IntoIter: ExactSizeIterator;
}

/// A trait for a store ID containing single items which can be used to access a
/// store in `STORES`.
pub trait SingleStoreValue: Sized {
    type Id: StoreId;

    /// Create a new value in the store from the given function.
    fn create_from(x: impl Into<Self>) -> Self::Id {
        Self::create_with(|_| x.into())
    }

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

/// Automatically implement [`StoreId`] and [`SequenceStoreValue`] for a
/// sequence store ID type.
#[macro_export]
macro_rules! static_sequence_store_indirect {
    (
        store = $store_vis:vis $store:ident,
        id = $id_vis:vis $id:ident[$el_id:ident],
        store_name = $store_name:ident,
        store_source = $store_source:expr
    ) => {
        $store_vis type $store = $crate::store::statics::DefaultIndirectSequenceStore<$id, $el_id>;
        $crate::new_sequence_store_key_indirect!($id_vis $id, $el_id);

        impl $crate::store::statics::StoreId for $id {
            type Value = Vec<$el_id>;
            type ValueRef = [$el_id];
            type ValueBorrow = $crate::store::sequence::SequenceStoreBorrowHandle<'static, [$el_id]>;
            type ValueBorrowMut = $crate::store::sequence::SequenceStoreBorrowMutHandle<'static, [$el_id]>;

            fn borrow(self) -> Self::ValueBorrow {
                use $crate::store::SequenceStore;
                $store_source.$store_name().borrow(self)
            }

            fn borrow_mut(self) -> Self::ValueBorrowMut {
                use $crate::store::SequenceStore;
                $store_source.$store_name().borrow_mut(self)
            }

            fn value(self) -> Self::Value {
                use $crate::store::SequenceStore;
                $store_source.$store_name().get_vec(self)
            }

            fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R {
                use $crate::store::SequenceStore;
                $store_source.$store_name().map_fast(self, f)
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R {
                use $crate::store::SequenceStore;
                $store_source.$store_name().modify_fast(self, f)
            }

            fn set(self, value: Self::Value) {
                use $crate::store::SequenceStore;
                $store_source.$store_name().set_from_slice_cloned(self, &value);
            }
        }

        impl $crate::store::statics::SequenceStoreValue for $el_id {
            type Id = $id;
            type ElementId = $el_id;

            fn empty_seq() -> Self::Id {
                use $crate::store::SequenceStore;
                $store_source.$store_name().create_from_slice(&[])
            }

            fn seq<I: IntoIterator<Item = Self>>(values: I) -> Self::Id
            where
                I::IntoIter: ExactSizeIterator,
            {
                use $crate::store::SequenceStore;
                $store_source.$store_name().create_from_iter(values)
            }
        }

        impl std::fmt::Debug for $id {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_list().entries(self.value().iter()).finish()
            }
        }

        use $crate::store::statics::StoreId;

        impl From<($id, usize)> for $el_id {
            fn from((id, index): ($id, usize)) -> Self {
                $id::from(id).map(|value| value[index].clone())
            }
        }
    };
}

/// Automatically implement `StoreId` and `SequenceStoreValue` for a sequence
/// store ID type.
#[macro_export]
macro_rules! static_sequence_store_direct {
    (
        store = $store_vis:vis $store:ident,
        id = $id_vis:vis $id:ident[$el_id:ident],
        value = $value:ty,
        store_name = $store_name:ident,
        store_source = $store_source:expr,
        derives = Debug
    ) => {
        static_sequence_store_direct! {
            store = $store_vis $store,
            id = $id_vis $id[$el_id],
            value = $value,
            store_name = $store_name,
            store_source = $store_source
        }
        $crate::impl_debug_for_sequence_store_element_key!($el_id);
    };
    (
        store = $store_vis:vis $store:ident,
        id = $id_vis:vis $id:ident[$el_id:ident],
        value = $value:ty,
        store_name = $store_name:ident,
        store_source = $store_source:expr
        $(, derives = $($extra_derives:ident),*)?
    ) => {
        $store_vis type $store = $crate::store::sequence::DefaultSequenceStore<$id, $value>;
        $crate::new_sequence_store_key_direct!($id_vis $id, $el_id $(, el_derives = [$($extra_derives),*])?);

        impl $crate::store::statics::StoreId for $id {
            type Value = Vec<$value>;
            type ValueRef = [$value];
            type ValueBorrow = $crate::store::sequence::SequenceStoreBorrowHandle<'static, [$value]>;
            type ValueBorrowMut = $crate::store::sequence::SequenceStoreBorrowMutHandle<'static, [$value]>;

            fn borrow(self) -> Self::ValueBorrow {
                $crate::store::SequenceStore::borrow($store_source.$store_name(), self)
            }

            fn borrow_mut(self) -> Self::ValueBorrowMut {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().borrow_mut(self)
            }

            fn value(self) -> Self::Value {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().get_vec(self)
            }

            fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().map_fast(self, f)
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().modify_fast(self, f)
            }

            fn set(self, value: Self::Value) {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().set_from_slice_cloned(self, &value);
            }
        }

        impl std::fmt::Debug for $id {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                use $crate::store::sequence::TrivialSequenceStoreKey;
                let entries: Vec<_> = self.iter().collect();
                f.debug_tuple(stringify!($id)).field(&self.index).field(&self.len)
                    .field(&entries)
                    .finish()
            }
        }

        impl $crate::store::statics::SequenceStoreValue for $value {
            type Id = $id;
            type ElementId = $el_id;

            fn empty_seq() -> Self::Id {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().create_from_slice(&[])
            }

            fn seq<I: IntoIterator<Item = Self>>(values: I) -> Self::Id
            where
                I::IntoIter: ExactSizeIterator,
            {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().create_from_iter(values)
            }
        }

        impl $crate::store::statics::StoreId for $el_id {
            type Value = $value;
            type ValueRef = $value;
            type ValueBorrow = $crate::store::sequence::SequenceStoreBorrowHandle<'static, $value>;
            type ValueBorrowMut = $crate::store::sequence::SequenceStoreBorrowMutHandle<'static, $value>;

            fn borrow(self) -> Self::ValueBorrow {
                use $crate::store::sequence::TrivialKeySequenceStore;
                $store_source.$store_name().borrow_element(self)
            }

            fn borrow_mut(self) -> Self::ValueBorrowMut {
                use $crate::store::sequence::TrivialKeySequenceStore;
                $store_source.$store_name().borrow_element_mut(self)
            }

            fn value(self) -> Self::Value {
                use $crate::store::sequence::TrivialKeySequenceStore;
                $store_source.$store_name().get_element(self.into())
            }

            fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R {
                use $crate::store::Store;
                $store_source.$store_name().map_fast(self.0, |v| f(&v[self.1]))
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R {
                use $crate::store::Store;
                $store_source.$store_name().modify_fast(self.0, |v| f(&mut v[self.1]))
            }

            fn set(self, value: Self::Value) {
                use $crate::store::Store;
                $store_source.$store_name().set_at_index(self.0, self.1, value);
            }
        }
    };
}

/// Automatically implement `StoreId` and `SingleStoreValue` for a single store
/// ID type.
#[macro_export]
macro_rules! static_single_store {
    (
        store = $store_vis:vis $store:ident,
        id = $id_vis:vis $id:ident,
        value = $value:ty,
        store_name = $store_name:ident,
        store_source = $store_source:expr,
        derives = Debug
    ) => {
        static_single_store! {
            store = $store_vis $store,
            id = $id_vis $id,
            value = $value,
            store_name = $store_name,
            store_source = $store_source
        }
        $crate::impl_debug_for_store_key!($id);
    };
    (
        store = $store_vis:vis $store:ident,
        id = $id_vis:vis $id:ident,
        value = $value:ty,
        store_name = $store_name:ident,
        store_source = $store_source:expr
        $(, derives = $($extra_derives:ident),*)?) => {
        $store_vis type $store = $crate::store::DefaultStore<$id, $value>;
        $crate::new_store_key!($id_vis $id $(, derives = $($extra_derives),*)?);

        impl $crate::store::statics::StoreId for $id {
            type Value = $value;
            type ValueRef = $value;
            type ValueBorrow = $crate::store::StoreBorrowHandle<'static, $value>;
            type ValueBorrowMut = $crate::store::StoreBorrowMutHandle<'static, $value>;

            fn borrow(self) -> Self::ValueBorrow {
                use hash_storage::store::Store;
                $crate::store::Store::borrow($store_source.$store_name(), self)
            }

            fn borrow_mut(self) -> Self::ValueBorrowMut {
                use $crate::store::Store;
                $store_source.$store_name().borrow_mut(self)
            }

            fn value(self) -> Self::Value {
                use $crate::store::CloneStore;
                $store_source.$store_name().get(self)
            }

            fn map<R>(self, f: impl FnOnce(&Self::Value) -> R) -> R {
                use $crate::store::Store;
                $store_source.$store_name().map_fast(self, f)
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::Value) -> R) -> R {
                use $crate::store::Store;
                $store_source.$store_name().modify_fast(self, f)
            }

            fn set(self, value: Self::Value) {
                use $crate::store::CloneStore;
                $store_source.$store_name().set(self, value);
            }
        }

        impl $crate::store::statics::SingleStoreValue for $value {
            type Id = $id;
            fn create_with<F: FnOnce(Self::Id) -> Self>(value: F) -> Self::Id {
                use $crate::store::Store;
                $store_source.$store_name().create_with(value)
            }
        }
    };
}

/// Automatically implement `StoreId` and `SingleStoreValue` for a single store
/// ID type.
#[macro_export]
macro_rules! static_partial_store {
    (
        store = $store_vis:vis $store:ident,
        id = $id_vis:vis $id:ident,
        value = $value:ty,
        store_name = $store_name:ident,
        store_source = $store_source:expr,
        derives = Debug
    ) => {
        static_partial_store! {
            store = $store_vis $store,
            id = $id_vis $id,
            value = $value,
            store_name = $store_name,
            store_source = $store_source
        }
        $crate::impl_debug_for_store_key!($id);
    };
    (
        store = $store_vis:vis $store:ident,
        id = $id_vis:vis $id:ident,
        value = $value:ty,
        store_name = $store_name:ident,
        store_source = $store_source:expr
        $(, derives = $($extra_derives:ident),*)?) => {
        $store_vis type $store = $crate::store::DefaultPartialStore<$id, $value>;

        impl $crate::store::statics::PartialStoreId for $id {
            type Value = $value;
            type ValueRef = $value;
            type ValueBorrow = $crate::store::partial::PartialStoreBorrowHandle<'static, $id, $value>;
            type ValueBorrowMut = $crate::store::partial::PartialStoreBorrowMutHandle<'static, $id, $value>;

            fn borrow(self) -> Option<Self::ValueBorrow> {
                use $crate::store::PartialStore;
                $crate::store::partial::PartialStore::borrow($store_source.$store_name(), self)
            }

            fn borrow_mut(self) -> Option<Self::ValueBorrowMut> {
                use $crate::store::PartialStore;
                $store_source.$store_name().borrow_mut(self)
            }

            fn value(self) -> Option<Self::Value> {
                use $crate::store::PartialCloneStore;
                $store_source.$store_name().get(self)
            }

            fn map<R>(self, f: impl FnOnce(Option<&Self::Value>) -> R) -> R {
                use $crate::store::PartialStore;
                $store_source.$store_name().map_fast(self, f)
            }

            fn modify<R>(self, f: impl FnOnce(Option<&mut Self::Value>) -> R) -> R {
                use $crate::store::PartialStore;
                $store_source.$store_name().modify_fast(self, f)
            }

            fn insert(self, value: Self::Value) {
                use $crate::store::PartialStore;
                $store_source.$store_name().insert(self, value);
            }

            fn exists(self) -> bool {
                use $crate::store::PartialStore;
                $store_source.$store_name().has(self)
            }
        }
    };
}
