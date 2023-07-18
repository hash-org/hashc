//! Defines a partial store which may or may not have a value for every key.
//! This is useful for storing partial information that is filled in as the
//! something is being processed, or to only store information for items that
//! require such storage.

use std::hash::Hash;

use dashmap::{
    mapref::one::{Ref, RefMut},
    DashMap,
};
use fxhash::FxBuildHasher;

/// The internal data structure for a [`PartialStore`].
pub type PartialStoreInternalData<Key, Value> = DashMap<Key, Value, FxBuildHasher>;
pub type PartialStoreBorrowHandle<'a, Key, Value> = Ref<'a, Key, Value, FxBuildHasher>;
pub type PartialStoreBorrowMutHandle<'a, Key, Value> = RefMut<'a, Key, Value, FxBuildHasher>;

/// A partial store, which provides a way to store values indexed by existing
/// keys. Unlike [`Store`], not every instance of `Key` necessarily has a value
/// in a [`PartialStore<Key, _>`].
///
/// Use [`new_partial_store`] to make a new partial store.
///
/// Like [`Store`], this data structure has interior mutability and so all of
/// its methods take `&self`. This makes it easy to use from within contexts
/// without having to worry too much about borrowing rules.
///
/// *Warning*: The `Value`'s `Clone` implementation must not interact with the
/// store, otherwise it might lead to a panic.
pub trait PartialStore<Key: Copy + Eq + Hash, Value> {
    fn internal_data(&self) -> &PartialStoreInternalData<Key, Value>;

    /// Insert a key-value pair inside the store, returning the old value if it
    /// exists.
    fn insert(&self, key: Key, value: Value) -> Option<Value> {
        self.internal_data().insert(key, value)
    }

    /// Whether the store has the given key.
    fn has(&self, key: Key) -> bool {
        self.internal_data().contains_key(&key)
    }

    /// Get a value by a key, and map it to another value given its reference,
    /// if it exists.
    ///
    /// *Warning*: Do not call mutating store methods (`create` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`Self::map()`] instead.
    fn map_fast<T>(&self, key: Key, f: impl FnOnce(Option<&Value>) -> T) -> T {
        let data = self.internal_data();
        let value = data.get(&key);
        match value {
            Some(value) => f(Some(value.value())),
            None => f(None),
        }
    }

    /// Modify a value by a key, possibly returning another value, if it exists.
    ///
    /// *Warning*: Do not call mutating store methods (`create` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`Self::modify()`] instead.
    fn modify_fast<T>(&self, key: Key, f: impl FnOnce(Option<&mut Value>) -> T) -> T {
        let data = self.internal_data();
        let value = data.get_mut(&key);
        match value {
            Some(mut value) => f(Some(value.value_mut())),
            None => f(None),
        }
    }

    /// Borrow a value mutably, given a key. Returns an appropriate handle which
    /// implements `DerefMut` to the value.
    fn borrow_mut(&self, key: Key) -> PartialStoreBorrowMutHandle<'_, Key, Value> {
        self.internal_data().get_mut(&key).unwrap()
    }

    /// Borrow a value, given a key. Returns an appropriate handle which
    /// implements `Deref` to the value.
    fn borrow(&self, key: Key) -> PartialStoreBorrowHandle<'_, Key, Value> {
        self.internal_data().get(&key).unwrap()
    }

    /// The number of entries in the store.
    fn len(&self) -> usize {
        self.internal_data().len()
    }

    /// Whether the store is empty.
    fn is_empty(&self) -> bool {
        self.internal_data().is_empty()
    }

    /// Clear the store of all key-value pairs.
    fn clear(&self) {
        self.internal_data().clear()
    }
}

/// Extra methods for [`PartialStore`] that require the `Value` to be `Clone`.
pub trait PartialCloneStore<Key: Copy + Eq + Hash, Value: Clone>: PartialStore<Key, Value> {
    /// Get a value by its key, if it exists.
    fn get(&self, key: Key) -> Option<Value> {
        self.internal_data().get(&key).map(|x| x.value().clone())
    }

    /// Get a value by a key, and map it to another value given its reference,
    /// if it exists.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create` etc). If you do not need to modify the
    /// store, consider using [`Self::map_fast()`] instead.
    fn map<T>(&self, key: Key, f: impl FnOnce(Option<&Value>) -> T) -> T {
        let value = self.get(key);
        f(value.as_ref())
    }

    /// Modify a value by a key, possibly returning another value, if it exists.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create` etc). If you do not need to modify the
    /// store, consider using [`Self::modify_fast()`] instead.
    fn modify<T>(&self, key: Key, f: impl FnOnce(Option<&mut Value>) -> T) -> T {
        let mut value = self.get(key);
        let ret = f(value.as_mut());
        if let Some(value) = value {
            self.insert(key, value);
        }
        ret
    }

    /// Duplicate a value in the store, returning the new key.
    ///
    /// Assumes that the key already exists in the store.
    fn duplicate(&self, from: Key, to: Key) {
        if let Some(value) = self.get(from) {
            self.insert(to, value);
        }
    }
}

impl<Key: Copy + Eq + Hash, Value: Clone, T: PartialStore<Key, Value>> PartialCloneStore<Key, Value>
    for T
{
}

/// A default implementation of [`PartialStore`].
#[derive(Debug)]
pub struct DefaultPartialStore<K: Eq + Hash, V> {
    data: PartialStoreInternalData<K, V>,
}

impl<K: Eq + Hash, V> Default for DefaultPartialStore<K, V> {
    fn default() -> Self {
        Self { data: DashMap::with_hasher(FxBuildHasher::default()) }
    }
}

impl<K: Eq + Hash, V> DefaultPartialStore<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: Copy + Eq + Hash, V> PartialStore<K, V> for DefaultPartialStore<K, V> {
    fn internal_data(&self) -> &PartialStoreInternalData<K, V> {
        &self.data
    }
}
