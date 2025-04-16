//! This defines a bunch of store variants (including single and sequence)
//! which can be used as a static store.

use super::DefaultSequenceStore;

/// A trait for a partial store ID indexing into a static store.
pub trait PartialStoreId {
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

/// A trait for a non-partial store ID indexing into a static store.
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

/// A marker specialisation of `StoreId` for a sequence store.
pub trait SequenceStoreId: StoreId {}

/// A marker specialisation of `StoreId` for a single store.
pub trait SingleStoreId: StoreId {}

/// A trait for a sequence store ID which can be used to access a store in
/// `STORES`.
pub trait SequenceStoreValue: Sized {
    type Id: SequenceStoreId;
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
    type Id: SingleStoreId;

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

/// The data structure for indirect sequence stores is the same as general
/// sequence stores.
pub type DefaultIndirectSequenceStore<K, V> = DefaultSequenceStore<K, V>;

/// Access the field `$member` of the value pointed to by `$id`.
#[macro_export]
macro_rules! get {
    ($id:expr, $member:ident) => {{ $crate::store::statics::StoreId::map($id, |x| x.$member) }};
}

/// Implement the trait `PartialStoreId` for the given types.
///
/// The `self_lam` parameter is used to map `self` to the actual store key.
#[macro_export]
macro_rules! impl_partial_store_id_for {
    (
        id = $id:ty,
        value = $value:ty,
        store_name = $store_name:ident,
        store_source = $store_source:expr,
        self_lam = $self:expr,
    ) => {
        impl $crate::store::statics::PartialStoreId for $id {
            type Value = $value;
            type ValueRef = $value;
            type ValueBorrow =
                $crate::store::partial::PartialStoreBorrowHandle<'static, $id, $value>;
            type ValueBorrowMut =
                $crate::store::partial::PartialStoreBorrowMutHandle<'static, $id, $value>;

            fn borrow(self) -> Option<Self::ValueBorrow> {
                use $crate::store::PartialStore;
                $crate::store::partial::PartialStore::borrow(
                    $store_source.$store_name(),
                    $self(self),
                )
            }

            fn borrow_mut(self) -> Option<Self::ValueBorrowMut> {
                use $crate::store::PartialStore;
                $store_source.$store_name().borrow_mut($self(self))
            }

            fn value(self) -> Option<Self::Value> {
                use $crate::store::PartialCloneStore;
                $store_source.$store_name().get($self(self))
            }

            fn map<R>(self, f: impl FnOnce(Option<&Self::Value>) -> R) -> R {
                use $crate::store::PartialStore;
                $store_source.$store_name().map_fast($self(self), f)
            }

            fn modify<R>(self, f: impl FnOnce(Option<&mut Self::Value>) -> R) -> R {
                use $crate::store::PartialStore;
                $store_source.$store_name().modify_fast($self(self), f)
            }

            fn insert(self, value: Self::Value) {
                use $crate::store::PartialStore;
                $store_source.$store_name().insert($self(self), value);
            }

            fn exists(self) -> bool {
                use $crate::store::PartialStore;
                $store_source.$store_name().has($self(self))
            }
        }
    };
}

/// Implement the trait `SingleStoreId` for the given types.
///
/// The `self_lam` parameter is used to map `self` to the actual store key.
#[macro_export]
macro_rules! impl_single_store_id_for {
    (
        id = $id:ty,
        value = $value:ty,
        store_name = $store_name:ident,
        store_source = $store_source:expr,
        self_lam = $self:expr,
    ) => {
        impl $crate::store::statics::SingleStoreId for $id {}
        impl $crate::store::statics::StoreId for $id {
            type Value = $value;
            type ValueRef = $value;
            type ValueBorrow = $crate::store::StoreBorrowHandle<'static, $value>;
            type ValueBorrowMut = $crate::store::StoreBorrowMutHandle<'static, $value>;

            fn borrow(self) -> Self::ValueBorrow {
                use hash_storage::store::Store;
                $crate::store::Store::borrow($store_source.$store_name(), $self(self))
            }

            fn borrow_mut(self) -> Self::ValueBorrowMut {
                use $crate::store::Store;
                $store_source.$store_name().borrow_mut($self(self))
            }

            fn value(self) -> Self::Value {
                use $crate::store::CloneStore;
                $store_source.$store_name().get($self(self))
            }

            fn map<R>(self, f: impl FnOnce(&Self::Value) -> R) -> R {
                use $crate::store::Store;
                $store_source.$store_name().map_fast($self(self), f)
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::Value) -> R) -> R {
                use $crate::store::Store;
                $store_source.$store_name().modify_fast($self(self), f)
            }

            fn set(self, value: Self::Value) {
                use $crate::store::CloneStore;
                $store_source.$store_name().set($self(self), value);
            }
        }
    };
}

/// Implement the trait `SequenceStoreId` for the given types.
///
/// The `self_lam` parameter is used to map `self` to the actual store key.
#[macro_export]
macro_rules! impl_sequence_store_id_for {
    (
        id = $id:ty,
        value = $value:ty,
        store_name = $store_name:ident,
        store_source = $store_source:expr,
        self_lam = $self:expr,
    ) => {
        impl $crate::store::statics::SequenceStoreId for $id {}
        impl $crate::store::statics::StoreId for $id {
            type Value = Vec<$value>;
            type ValueRef = [$value];
            type ValueBorrow =
                $crate::store::sequence::SequenceStoreBorrowHandle<'static, [$value]>;
            type ValueBorrowMut =
                $crate::store::sequence::SequenceStoreBorrowMutHandle<'static, [$value]>;

            fn borrow(self) -> Self::ValueBorrow {
                $crate::store::SequenceStore::borrow($store_source.$store_name(), $self(self))
            }

            fn borrow_mut(self) -> Self::ValueBorrowMut {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().borrow_mut($self(self))
            }

            fn value(self) -> Self::Value {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().get_vec($self(self))
            }

            fn map<R>(self, f: impl FnOnce(&Self::ValueRef) -> R) -> R {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().map_fast($self(self), f)
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().modify_fast($self(self), f)
            }

            fn set(self, value: Self::Value) {
                use $crate::store::sequence::SequenceStore;
                $store_source.$store_name().set_from_slice_cloned($self(self), &value);
            }
        }
    };
}

/// Define a static single store with the given specifications.
///
/// This will create a `$store: Store<$id, $value>`, where `$id` is
/// a generated type. Furthermore, it will implement `SingleStoreId` for `$id`
/// by accessing the global `$store_source.$store_name()`, and will implement
/// `SingleStoreValue` for `$value`.
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
        $(, derives = $($extra_derives:ident),*)?
    ) => {
        // Create the store
        $store_vis type $store = $crate::store::DefaultStore<$id, $value>;
        // Create the store key
        $crate::new_store_key!($id_vis $id $(, derives = $($extra_derives),*)?);
        // Implement `SingleStoreId` for `$id`
        $crate::impl_single_store_id_for!(
            id = $id,
            value = $value,
            store_name = $store_name,
            store_source = $store_source,
            self_lam = |s| s,
        );
        // Implement `SingleStoreValue` for `$value`
        impl $crate::store::statics::SingleStoreValue for $value {
            type Id = $id;
            fn create_with<F: FnOnce(Self::Id) -> Self>(value: F) -> Self::Id {
                use $crate::store::Store;
                $store_source.$store_name().create_with(value)
            }
        }
    };
}

/// Define a static partial store with the given specifications.
///
/// This will create a `$store: PartialStore<$id, $value>`, where `$id` is
/// a generated type. Furthermore, it will implement `PartialStoreId` for `$id`
/// by accessing the global `$store_source.$store_name()`.
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
        $(, derives = $($extra_derives:ident),*)?
    ) => {
        // Create the store
        $store_vis type $store = $crate::store::DefaultPartialStore<$id, $value>;
        // Implement `PartialStoreId` for `$id`
        $crate::impl_partial_store_id_for!(
            id = $id,
            value = $value,
            store_name = $store_name,
            store_source = $store_source,
            self_lam = |s| s,
        );
    };
}

/// Define a static indirect sequence store with the given specifications.
///
/// This will create a `$store: SequenceStore<$id, $el_id>`, where `$id` is
/// a generated type. Furthermore, it will implement `SequenceStoreId` for `$id`
/// by accessing the global `$store_source.$store_name()`, and
/// `SequenceStoreValue` for `$el_id`.
#[macro_export]
macro_rules! static_sequence_store_indirect {
    (
        store = $store_vis:vis $store:ident,
        id = $id_vis:vis $id:ident[$el_id:ident],
        store_name = $store_name:ident,
        store_source = $store_source:expr
    ) => {
        // Create the store
        $store_vis type $store = $crate::store::statics::DefaultIndirectSequenceStore<$id, $el_id>;
        // Create the store key type
        $crate::new_sequence_store_key_indirect!($id_vis $id, $el_id);

        // Implement `SequenceStoreId` for `$id`
        $crate::impl_sequence_store_id_for! {
            id = $id,
            value = $el_id,
            store_name = $store_name,
            store_source = $store_source,
            self_lam = |s| s,
        }

        // Implement `SequenceStoreValue` for `$el_id`
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
                use $crate::store::statics::StoreId;
                f.debug_list().entries(self.value().iter()).finish()
            }
        }

        use $crate::store::statics::SingleStoreId;

        impl From<($id, usize)> for $el_id {
            fn from((id, index): ($id, usize)) -> Self {
                use $crate::store::statics::StoreId;
                $id::from(id).map(|value| value[index].clone())
            }
        }
    };
}

/// Define a static direct sequence store with the given specifications.
///
/// This will create a `$store: SequenceStore<$id, $value>`, where `$id` and
/// `$el_id` is a generated type. Furthermore, it will implement
/// `SequenceStoreId` for `$id` by accessing the global
/// `$store_source.$store_name()`, as well as `SingleStoreId` for `$el_id` that
/// accesses elements of the sequence.  Finally, it will implement
/// `SequenceStoreValue` for `$value`.
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
        // Create the store
        $store_vis type $store = $crate::store::sequence::DefaultSequenceStore<$id, $value>;
        // Create the store sequence and element keys
        $crate::new_sequence_store_key_direct!($id_vis $id, $el_id $(, el_derives = [$($extra_derives),*])?);

        // Implement `SequenceStoreId` for `$id`
        $crate::impl_sequence_store_id_for! {
            id = $id,
            value = $value,
            store_name = $store_name,
            store_source = $store_source,
            self_lam = |s| s,
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
        // Implement `SequenceStoreValue` for `$value`
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

        // Use `$el_id` as a single store ID, by indexing into the sequence:
        impl $crate::store::statics::SingleStoreId for $el_id { }
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
                use $crate::store::SequenceStore;
                $store_source.$store_name().map_fast(self.0, |v| f(&v[self.1 as usize]))
            }

            fn modify<R>(self, f: impl FnOnce(&mut Self::ValueRef) -> R) -> R {
                use $crate::store::SequenceStore;
                $store_source.$store_name().modify_fast(self.0, |v| f(&mut v[self.1 as usize]))
            }

            fn set(self, value: Self::Value) {
                use $crate::store::SequenceStore;
                $store_source.$store_name().set_at_index(self.0, self.1 as usize, value);
            }
        }
    };
}
