//! Defines the base traits and macros for creating [`Store`]s.
use std::marker::PhantomData;

use parking_lot::{
    MappedRwLockReadGuard, MappedRwLockWriteGuard, RwLock, RwLockReadGuard, RwLockWriteGuard,
};

/// Represents a key that can be used to index a [`Store`].
pub trait StoreKey: Copy + Eq {
    /// Turn the key into an index.
    fn to_index(self) -> usize;
    /// Create a key from an index.
    ///
    /// This should generally not be used in client code.
    fn from_index_unchecked(index: usize) -> Self;
}

/// Create a new [`StoreKey`] with the given name.
#[macro_export]
macro_rules! new_store_key {
    ($visibility:tt $name:ident $(, derives = $($extra_derives:ident),*)?) => {
        #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, $($($extra_derives),*)?)]
        $visibility struct $name {
            index: u32,
        }

        impl $crate::store::StoreKey for $name {

            fn to_index(self) -> usize {
                self.index.try_into().unwrap()
            }

            fn from_index_unchecked(index: usize) -> Self {
                Self { index: index.try_into().unwrap() }
            }
        }
    };
}

#[macro_export]
macro_rules! impl_debug_for_store_key {
    ($name:ident) => {
        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_tuple(stringify!($name)).field(&self.index).finish()
            }
        }
    };
}

/// The internal data of a store.
pub type StoreInternalData<Value> = RwLock<Vec<Value>>;
pub type StoreBorrowHandle<'a, Value> = MappedRwLockReadGuard<'a, Value>;
pub type StoreBorrowMutHandle<'a, Value> = MappedRwLockWriteGuard<'a, Value>;

/// A store, which provides a way to efficiently store values indexed by opaque
/// generated keys.
///
/// Use [`new_store_key`] to make such a key type, and [`new_store`] to make a
/// store.
///
/// This trait operates on interior mutability and so all of its methods take
/// `&self`. This makes it easy to use from within contexts without having to
/// worry too much about borrowing rules.
///
/// *Warning*: The `Value`'s `Clone` implementation must not interact with the
/// store, otherwise it might lead to a panic.
pub trait Store<Key: StoreKey, Value> {
    /// Get a reference to the internal data of the store.
    ///
    /// This should only be used to implement new store methods, not to access
    /// the store.
    fn internal_data(&self) -> &StoreInternalData<Value>;

    /// Create a value inside the store, given its key, returning its key.
    fn create_with(&self, value_fn: impl FnOnce(Key) -> Value) -> Key {
        let mut data = self.internal_data().write();
        let next_index = data.len();
        let key = Key::from_index_unchecked(next_index);
        let value = value_fn(key);
        data.push(value);
        key
    }

    /// Create a value inside the store, returning its key.
    fn create(&self, value: Value) -> Key {
        let mut data = self.internal_data().write();
        let next_index = data.len();
        data.push(value);
        Key::from_index_unchecked(next_index)
    }

    /// Get a value by a key, and map it to another value given its reference.
    ///
    /// *Warning*: Do not call mutating store methods (`create` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`CloneStore::map()`] instead.
    fn map_fast<T>(&self, key: Key, f: impl FnOnce(&Value) -> T) -> T {
        let data = self.internal_data().read();
        let value = data.get(key.to_index()).unwrap();
        f(value)
    }

    /// Get many values by a collection of keys, and map them to another value.
    ///
    /// *Warning*: Do not call mutating store methods (`create` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`CloneStore::map_many()`] instead.
    fn map_many_fast<T>(
        &self,
        keys: impl IntoIterator<Item = Key>,
        f: impl FnOnce(&[&Value]) -> T,
    ) -> T {
        let data = self.internal_data().read();
        let values =
            keys.into_iter().map(|key| data.get(key.to_index()).unwrap()).collect::<Vec<_>>();
        f(&values)
    }

    /// Borrow a value mutably, given a key. Returns an appropriate handle which
    /// implements `DerefMut` to the value.
    fn borrow_mut(&self, key: Key) -> StoreBorrowMutHandle<'_, Value> {
        let data = self.internal_data().write();
        RwLockWriteGuard::map(data, |d| d.get_mut(key.to_index()).unwrap())
    }

    /// Borrow a value, given a key. Returns an appropriate handle which
    /// implements `Deref` to the value.
    fn borrow(&self, key: Key) -> StoreBorrowHandle<'_, Value> {
        let data = self.internal_data().read();
        RwLockReadGuard::map(data, |d| d.get(key.to_index()).unwrap())
    }

    /// Modify a value by a key, possibly returning another value.
    ///
    /// *Warning*: Do not call mutating store methods (`create` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`CloneStore::modify()`] instead.
    fn modify_fast<T>(&self, key: Key, f: impl FnOnce(&mut Value) -> T) -> T {
        let mut data = self.internal_data().write();
        let value = data.get_mut(key.to_index()).unwrap();
        f(value)
    }
}

/// Additional functionality for [`Store`] when the value implements [`Clone`].
pub trait CloneStore<Key: StoreKey, Value: Clone>: Store<Key, Value> {
    /// Get a value by its key.
    fn get(&self, key: Key) -> Value {
        self.internal_data().read().get(key.to_index()).unwrap().clone()
    }

    /// Get a value by a key, and map it to another value given its reference.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create` etc). If you do not need to modify the
    /// store, consider using [`Store::map_fast()`] instead.
    fn map<T>(&self, key: Key, f: impl FnOnce(&Value) -> T) -> T {
        let value = self.get(key);
        f(&value)
    }

    /// Modify a value by a key, possibly returning another value.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create` etc). If you do not need to modify the
    /// store, consider using [`Store::modify_fast()`] instead.
    fn modify<T>(&self, key: Key, f: impl FnOnce(&mut Value) -> T) -> T {
        let mut value = self.get(key);
        let ret = f(&mut value);
        self.set(key, value);
        ret
    }

    /// Set a key's value to a new value, returning the old value.
    fn set(&self, key: Key, new_value: Value) -> Value {
        let mut data = self.internal_data().write();
        let value_ref = data.get_mut(key.to_index()).unwrap();
        let old_value = value_ref.clone();
        *value_ref = new_value;
        old_value
    }
}

impl<Key: StoreKey, Value: Clone, S: Store<Key, Value>> CloneStore<Key, Value> for S {}

/// A default implementation of [`Store`].
#[derive(Debug)]
pub struct DefaultStore<K, V> {
    data: StoreInternalData<V>,
    _phantom: PhantomData<K>,
}

impl<K, V> std::default::Default for DefaultStore<K, V> {
    fn default() -> Self {
        Self { data: RwLock::new(Vec::new()), _phantom: PhantomData }
    }
}

impl<K, V> DefaultStore<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: StoreKey, V: Clone> Store<K, V> for DefaultStore<K, V> {
    fn internal_data(&self) -> &StoreInternalData<V> {
        &self.data
    }
}

#[cfg(test)]
mod test_super {
    // Ensuring macros expand correctly:
    new_store_key!(pub TestK);
}
