//! Provides generic data structures to store values by generated keys in an
//! efficient way, with interior mutability.

// @@Organisation: Move this module to the `hash_alloc` crate and split it into
// smaller modules.
use std::{
    hash::Hash,
    iter::{repeat, Map, Repeat, Zip},
    marker::PhantomData,
    ops::Range,
};

use append_only_vec::AppendOnlyVec;
use dashmap::DashMap;
use fxhash::FxBuildHasher;
pub use fxhash::{FxHashMap, FxHashSet};
use parking_lot::RwLock;

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
        let next_index = self.internal_data().read().len();
        let key = Key::from_index_unchecked(next_index);
        let value = value_fn(key);
        let mut data = self.internal_data().write();
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

#[derive(Copy, Clone, Default, PartialEq, Eq, Hash)]
pub struct SequenceStoreElement<T>(pub T, pub usize);

impl<T> From<(T, usize)> for SequenceStoreElement<T> {
    fn from(value: (T, usize)) -> Self {
        SequenceStoreElement(value.0, value.1)
    }
}

pub type SequenceStoreKeyIter<T, K> = Map<Zip<Repeat<T>, Range<usize>>, fn((T, usize)) -> K>;

/// Represents a key that can be used to index a [`SequenceStore`].
pub trait SequenceStoreKey: Copy + Eq {
    type ElementKey: Copy + Eq;

    /// Turn the key into an index and a length.
    fn to_index_and_len(self) -> (usize, usize);

    /// Create a key from an index and a length.
    ///
    /// This should generally not be used in client code.
    fn from_index_and_len_unchecked(index: usize, len: usize) -> Self;

    /// Turn the key into an index range `0..len`.
    ///
    /// Can be used to iterate over the values of the key in conjunction with
    /// [`SequenceStore::get_at_index()`].
    fn to_index_range(self) -> Range<usize> {
        0..self.len()
    }

    /// Get the length of the entry corresponding to the key.
    fn len(self) -> usize {
        let (_, len) = self.to_index_and_len();
        len
    }

    /// Whether the sequence the key points to is empty.
    fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Get the index of the entry corresponding to the key.
    fn entry_index(self) -> usize {
        let (index, _) = self.to_index_and_len();
        index
    }

    /// Get an empty key.
    fn empty() -> Self {
        Self::from_index_and_len_unchecked(0, 0)
    }
}

pub trait TrivialSequenceStoreKey: SequenceStoreKey {
    type Iter: Iterator<Item = Self::ElementKey>;
    /// Turn the key into a range `(key, 0)..(key, len)`.
    fn iter(self) -> Self::Iter;
}

impl<T: SequenceStoreKey> TrivialSequenceStoreKey for T
where
    T::ElementKey: From<(T, usize)>,
{
    type Iter = SequenceStoreKeyIter<T, T::ElementKey>;
    fn iter(self) -> Self::Iter {
        repeat(self).zip(self.to_index_range()).map(Self::ElementKey::from)
    }
}

/// Create a new [`SequenceStoreKey`] with the given name.
#[macro_export]
macro_rules! new_sequence_store_key_indirect {
    ($visibility:vis $name:ident, $el_name:ident $(, derives = $($extra_derives:ident),*)?) => {
        #[derive(PartialEq, Eq, Clone, Copy, Hash, $($($extra_derives),*)?)]
        $visibility struct $name {
            index: u32,
            len: u32,
        }

        impl $crate::store::SequenceStoreKey for $name {
            type ElementKey = $el_name;

            fn to_index_and_len(self) -> (usize, usize) {
                (self.index.try_into().unwrap(), self.len.try_into().unwrap())
            }

            fn from_index_and_len_unchecked(index: usize, len: usize) -> Self {
                Self { index: index.try_into().unwrap(), len: len.try_into().unwrap() }
            }
        }
    };
}

#[macro_export]
macro_rules! impl_debug_for_sequence_store_key {
    ($name:ident) => {
        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_tuple(stringify!($name)).field(&self.index).field(&self.len).finish()
            }
        }
    };
}

#[macro_export]
macro_rules! impl_debug_for_sequence_store_element_key {
    ($name:ident) => {
        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_tuple(stringify!($name))
                    .field(&(&self.0.index, &self.0.len))
                    .field(&self.1)
                    .finish()
            }
        }
    };
}

/// Create a new [`SequenceStoreKey`] with the given name.
#[macro_export]
macro_rules! new_sequence_store_key_direct {
    ($visibility:vis $name:ident, $el_name:ident $(, derives = [$($extra_derives:ident),*])?  $(, el_derives = [$($extra_el_derives:ident),*])?) => {
        #[derive(PartialEq, Eq, Clone, Copy, Hash, $($($extra_derives),*)?)]
        $visibility struct $name {
            index: u32,
            len: u32,
        }

        #[derive(PartialEq, Eq, Clone, Copy, Hash, $($($extra_el_derives),*)?)]
        $visibility struct $el_name(pub $name, pub usize);

        impl From<$el_name> for ($name, usize) {
            fn from(value: $el_name) -> Self {
                (value.0, value.1)
            }
        }

        impl From<($name, usize)> for $el_name {
            fn from(value: ($name, usize)) -> Self {
                Self(value.0, value.1)
            }
        }

        impl $crate::store::SequenceStoreKey for $name {
            type ElementKey = $el_name;

            fn to_index_and_len(self) -> (usize, usize) {
                (self.index.try_into().unwrap(), self.len.try_into().unwrap())
            }

            fn from_index_and_len_unchecked(index: usize, len: usize) -> Self {
                Self { index: index.try_into().unwrap(), len: len.try_into().unwrap() }
            }
        }
    };
}

/// The internal data of a store.
pub type SequenceStoreInternalData<Value> = RwLock<Vec<Value>>;

/// A sequence store, which provides a way to efficiently store sequences of
/// contiguous values by an opaque generated key.
///
/// Use [`new_sequence_store_key`] to make such a key type, and
/// [`new_sequence_store`] to make a new sequence store.
///
/// Like [`Store`], this data structure has interior mutability and so all of
/// its methods take `&self`. This makes it easy to use from within contexts
/// without having to worry too much about borrowing rules.
///
/// *Warning*: The `Value`'s `Clone` implementation must not interact with the
/// store, otherwise it might lead to a panic.
pub trait SequenceStore<Key: SequenceStoreKey, Value: Clone> {
    /// Get a reference to the internal data of the store.
    ///
    /// This should only be used to implement new store methods, not to access
    /// the store.
    fn internal_data(&self) -> &SequenceStoreInternalData<Value>;

    /// Create a sequence of values inside the store from a slice, returning its
    /// key.
    fn create_from_slice(&self, values: &[Value]) -> Key {
        let mut data = self.internal_data().write();
        let starting_index = data.len();
        data.extend_from_slice(values);
        Key::from_index_and_len_unchecked(starting_index, values.len())
    }

    /// Create an empty sequence of values inside the store, returning its key.
    fn create_empty(&self) -> Key {
        let starting_index = self.internal_data().read().len();
        Key::from_index_and_len_unchecked(starting_index, 0)
    }

    /// Same as [`SequenceStore::create_from_iter()`], but each value takes its
    /// key and index.
    ///
    /// The given iterator must support [`ExactSizeIterator`].
    fn create_from_iter_with<F: FnOnce(Key::ElementKey) -> Value, I: IntoIterator<Item = F>>(
        &self,
        values: I,
    ) -> Key
    where
        I::IntoIter: ExactSizeIterator,
        Key::ElementKey: From<(Key, usize)>,
    {
        let starting_index = self.internal_data().read().len();

        let (key, values_computed) = {
            let values = values.into_iter();
            let key = Key::from_index_and_len_unchecked(starting_index, values.len());
            (
                key,
                values
                    .enumerate()
                    .map(|(i, f)| f(Key::ElementKey::from((key, i))))
                    .collect::<Vec<_>>(),
            )
        };

        let mut data = self.internal_data().write();
        data.extend(values_computed);
        key
    }

    /// Create a sequence of values inside the store from an iterator-like
    /// object, returning its key.
    ///
    /// *Warning*: Do not call mutating store methods (`create_*` etc) in the
    /// `values` iterator, otherwise there will be a panic. If you want to
    /// do this, consider using [`Self::create_from_iter()`] instead.
    fn create_from_iter_fast(&self, values: impl IntoIterator<Item = Value>) -> Key {
        let mut data = self.internal_data().write();
        let starting_index = data.len();
        data.extend(values);
        Key::from_index_and_len_unchecked(starting_index, data.len() - starting_index)
    }

    /// Create a sequence of values inside the store from an iterator-like
    /// object, returning its key.
    ///
    /// It is safe to provide an iterator-like object `values` to this function
    /// that modifies the store in some way (`create_*` etc). If you do not
    /// need to modify the store, consider using
    /// [`Self::create_from_iter_fast()`] instead.
    fn create_from_iter(&self, values: impl IntoIterator<Item = Value>) -> Key {
        let values = values.into_iter().collect::<Vec<_>>();
        self.create_from_slice(&values)
    }

    /// Try create a sequence of values inside the store from an iterator-like
    /// object, returning its key, or an error if it occurred.
    ///
    /// *Warning*: Do not call mutating store methods (`create_*` etc) in the
    /// `values` iterator, otherwise there will be a panic. If you want to
    /// do this, consider using [`Self::create_from_iter()`] instead.
    fn try_create_from_iter_fast<E>(
        &self,
        values: impl IntoIterator<Item = Result<Value, E>>,
    ) -> Result<Key, E> {
        let mut data = self.internal_data().write();
        let starting_index = data.len();
        let values = values.into_iter();

        // Mirroring the .extend() implementation:
        data.reserve(starting_index + values.size_hint().0.saturating_add(1));

        for value in values {
            match value {
                Ok(value) => {
                    data.push(value);
                }
                Err(err) => {
                    // Remove all currently added values and return the error:
                    data.truncate(starting_index);
                    return Err(err);
                }
            }
        }

        Ok(Key::from_index_and_len_unchecked(starting_index, data.len() - starting_index))
    }

    /// Try create a sequence of values inside the store from an iterator-like
    /// object, returning its key, or an error if it occurred.
    ///
    /// It is safe to provide an iterator-like object `values` to this function
    /// that modifies the store in some way (`create_*` etc). If you do not
    /// need to modify the store, consider using
    /// [`Self::create_from_iter_fast()`] instead.
    fn try_create_from_iter<E>(
        &self,
        values: impl IntoIterator<Item = Result<Value, E>>,
    ) -> Result<Key, E> {
        let values = values.into_iter().collect::<Result<Vec<_>, _>>()?;
        Ok(self.create_from_slice(&values))
    }

    /// Get the value at the given index in the value sequence corresponding to
    /// the given key.
    ///
    /// Panics if the index is out of bounds for the given key.
    fn get_at_index(&self, key: Key, index: usize) -> Value {
        let (starting_index, len) = key.to_index_and_len();
        assert!(index < len);
        self.internal_data().read().get(starting_index + index).unwrap().clone()
    }

    /// Get the value at the given index in the value sequence corresponding to
    /// the given key.
    ///
    /// Panics if the index is out of bounds for the given key.
    fn try_get_at_index(&self, key: Key, index: usize) -> Option<Value> {
        let (starting_index, _) = key.to_index_and_len();
        self.internal_data().read().get(starting_index + index).cloned()
    }

    /// Get the value sequence for the given key as an owned vector.
    fn get_vec(&self, key: Key) -> Vec<Value> {
        let (index, len) = key.to_index_and_len();
        self.internal_data().read().get(index..index + len).unwrap().to_vec()
    }

    /// Set the value at the given index in the value sequence corresponding to
    /// the given key, to the given value. Returns the original value.
    ///
    /// Panics if the index is out of bounds for the given key.
    fn set_at_index(&self, key: Key, index: usize, new_value: Value) -> Value {
        let (starting_index, len) = key.to_index_and_len();
        assert!(index < len);
        let mut data = self.internal_data().write();
        let value_ref = data.get_mut(starting_index + index).unwrap();
        let old_value = value_ref.clone();
        *value_ref = new_value;
        old_value
    }

    /// Set the value sequence corresponding to the given key, to the given
    /// slice.
    ///
    /// Panics if the slice is not the same size as the existing value.
    fn set_from_slice_cloned(&self, key: Key, new_value_sequence: &[Value]) {
        assert!(key.len() == new_value_sequence.len());
        let mut data = self.internal_data().write();
        let value_slice_ref = data.get_mut(key.to_index_range()).unwrap();
        value_slice_ref.clone_from_slice(new_value_sequence);
    }

    /// Get a value sequence by a key, and map it to another value given its
    /// slice.
    ///
    /// *Warning*: Do not call mutating store methods (`create_*` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`Self::map()`] instead.
    fn map_fast<T>(&self, key: Key, f: impl FnOnce(&[Value]) -> T) -> T {
        let data = self.internal_data().read();
        let (index, len) = key.to_index_and_len();
        let value = data.get(index..index + len).unwrap();
        f(value)
    }

    /// Get a value sequence by a key, and map it to another value given its
    /// slice.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create_*` etc). If you do not need to modify the
    /// store, consider using [`Self::map_fast()`] instead.
    fn map<T>(&self, key: Key, f: impl FnOnce(&[Value]) -> T) -> T {
        let value = self.get_vec(key);
        f(&value)
    }

    /// Modify a value sequence by a key, possibly returning another value.
    ///
    /// *Warning*: Do not call mutating store methods (`create_*` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`Self::modify_cloned()`] instead.
    fn modify_fast<T>(&self, key: Key, f: impl FnOnce(&mut [Value]) -> T) -> T {
        let mut data = self.internal_data().write();
        let (index, len) = key.to_index_and_len();
        let value = data.get_mut(index..index + len).unwrap();
        f(value)
    }

    /// Modify a value sequence by a key, possibly returning another value.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create_*` etc). If you do not need to modify the
    /// store, consider using [`Self::modify_fast()`] instead.
    fn modify_cloned<T>(&self, key: Key, f: impl FnOnce(&mut [Value]) -> T) -> T {
        let mut value = self.get_vec(key);
        let ret = f(&mut value);
        self.set_from_slice_cloned(key, &value);
        ret
    }
}

pub trait SequenceStoreCopy<Key: SequenceStoreKey, Value: Copy>: SequenceStore<Key, Value> {
    /// Set the value sequence corresponding to the given key, to the given
    /// slice. Uses `memcpy` to do this, given that the value implements `Copy`.
    ///
    /// Panics if the slice is not the same size as the existing value.
    fn set_from_slice_copied(&self, key: Key, new_value_sequence: &[Value]) {
        assert!(key.len() == new_value_sequence.len());
        let mut data = self.internal_data().write();
        let (index, len) = key.to_index_and_len();
        let value_slice_ref = data.get_mut(index..index + len).unwrap();
        value_slice_ref.copy_from_slice(new_value_sequence);
    }

    /// Modify a value sequence by a key, possibly returning another value.
    /// Uses `memcpy` to update the original sequence, given that the value
    /// implements `Copy`.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create_*` etc). If you do not need to modify the
    /// store, consider using `modify_fast()` instead.
    fn modify_copied<T>(&self, key: Key, f: impl FnOnce(&mut [Value]) -> T) -> T {
        let mut value = self.get_vec(key);
        let ret = f(&mut value);
        self.set_from_slice_copied(key, &value);
        ret
    }
}

impl<Key: SequenceStoreKey, Value: Copy, T: SequenceStore<Key, Value>> SequenceStoreCopy<Key, Value>
    for T
{
}

pub trait SequenceStoreIter<Key: SequenceStoreKey, Value: Clone> {
    type Iter<'s>
    where
        Self: 's,
        Key: 's;

    /// Iterate over the value sequence for the given key.
    ///
    /// It is safe to call mutating store methods (`create_*` etc) when mapping
    /// the iterator etc.
    fn iter(&self, key: Key) -> Self::Iter<'_>;
}

impl<Key: SequenceStoreKey, Value: Clone, T: SequenceStore<Key, Value>>
    SequenceStoreIter<Key, Value> for T
{
    type Iter<'s> = impl Iterator<Item = Value> + 's where T: 's, Key: 's;
    fn iter(&self, key: Key) -> Self::Iter<'_> {
        key.to_index_range().map(move |index| {
            self.internal_data().read().get(key.entry_index() + index).unwrap().clone()
        })
    }
}

pub trait TrivialKeySequenceStore<Key: SequenceStoreKey, Value: Clone>:
    SequenceStore<Key, Value>
{
    /// Same as [`SequenceStore::get_at_index`] but takes the element key and
    /// index as a tuple.
    fn get_element(&self, element_id: Key::ElementKey) -> Value;
}

impl<Key: SequenceStoreKey, Value: Clone, T: SequenceStore<Key, Value>>
    TrivialKeySequenceStore<Key, Value> for T
where
    Key::ElementKey: Into<(Key, usize)>,
{
    fn get_element(&self, element_id: Key::ElementKey) -> Value {
        let (key, index) = element_id.into();
        self.get_at_index(key, index)
    }
}

/// A default implementation of [`SequenceStore`].
#[derive(Debug)]
pub struct DefaultSequenceStore<K, V> {
    data: SequenceStoreInternalData<V>,
    _phantom: PhantomData<K>,
}

impl<K, V> Default for DefaultSequenceStore<K, V> {
    fn default() -> Self {
        Self { data: RwLock::new(Vec::new()), _phantom: PhantomData }
    }
}

impl<K, V> DefaultSequenceStore<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: SequenceStoreKey, V: Clone> SequenceStore<K, V> for DefaultSequenceStore<K, V> {
    fn internal_data(&self) -> &SequenceStoreInternalData<V> {
        &self.data
    }
}

/// The internal data structure for a [`PartialStore`].
pub type PartialStoreInternalData<Key, Value> = DashMap<Key, Value, FxBuildHasher>;

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

/// This store uses [`AppendOnlyVec`] internally, rather than a
/// [`StoreInternalData<_>`], so that there isn't additional overhead when
/// reading/writing elements; you can take references out of it. The trade-off
/// is that the value needs to implement [`Copy`].
///
/// N.B. This store does not support overwriting existing elements.
pub trait AppendOnlyStore<Key: StoreKey, Value: Copy> {
    /// Get a reference to the internal data of the store.
    ///
    /// This should only be used to implement new store methods, not to access
    /// the store.
    fn internal_data(&self) -> &AppendOnlyVec<Value>;

    /// Create a value inside the store, given its key, returning its key.
    fn create_with(&self, value_fn: impl FnOnce(Key) -> Value) -> Key {
        let data = self.internal_data();
        let next_index = data.len();
        let key = Key::from_index_unchecked(next_index);
        data.push(value_fn(key));
        key
    }

    /// Create a value inside the store, returning its key.
    fn create(&self, value: Value) -> Key {
        let data = self.internal_data();
        let next_index = data.len();
        data.push(value);
        Key::from_index_unchecked(next_index)
    }

    /// Get a reference to a value by its key, given that it exists.
    fn get(&self, key: Key) -> &Value {
        let data = self.internal_data();
        &data[key.to_index()]
    }
}

/// A default implementation of [`DefaultAppendOnlyStore`].
pub struct DefaultAppendOnlyStore<K, V> {
    data: AppendOnlyVec<V>,
    _phantom: PhantomData<K>,
}

impl<K, V> Default for DefaultAppendOnlyStore<K, V> {
    fn default() -> Self {
        Self { data: AppendOnlyVec::new(), _phantom: PhantomData }
    }
}

impl<K, V> DefaultAppendOnlyStore<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: StoreKey, V: Copy> AppendOnlyStore<K, V> for DefaultAppendOnlyStore<K, V> {
    fn internal_data(&self) -> &AppendOnlyVec<V> {
        &self.data
    }
}

/// This is the equivalent to [`AppendOnlyStore`] but for sequences of values.
///
/// Note that you cannot get slices of values from this store, as the values
/// are not necessarily stored contiguously in memory. You can, however, iterate
/// the sequence store key and read the corresponding value references using
/// [`SequenceAppendOnlyStore::get_element()`].
pub trait SequenceAppendOnlyStore<Key: SequenceStoreKey, Value: Copy> {
    /// Get a reference to the internal data of the store.
    ///
    /// This should only be used to implement new store methods, not to access
    /// the store.
    fn internal_data(&self) -> &AppendOnlyVec<Value>;

    /// Create a sequence inside the store from the given slice of values,
    /// returning its key.
    fn create_from_slice(&self, values: &[Value]) -> Key {
        let data = self.internal_data();
        let starting_index = data.len();
        for value in values {
            data.push(*value);
        }
        Key::from_index_and_len_unchecked(starting_index, values.len())
    }

    /// Create an empty sequence of values inside the store, returning its key.
    fn create_empty(&self) -> Key {
        let starting_index = self.internal_data().len();
        Key::from_index_and_len_unchecked(starting_index, 0)
    }

    /// Same as [`SequenceStore::create_from_iter()`], but each value takes its
    /// key and index.
    ///
    /// The given iterator must support [`ExactSizeIterator`].
    fn create_from_iter_with<F: FnOnce(Key::ElementKey) -> Value, I: IntoIterator<Item = F>>(
        &self,
        values: I,
    ) -> Key
    where
        I::IntoIter: ExactSizeIterator,
        Key::ElementKey: From<(Key, usize)>,
    {
        let starting_index = self.internal_data().len();

        let (key, values_computed) = {
            let values = values.into_iter();
            let key = Key::from_index_and_len_unchecked(starting_index, values.len());
            (key, values.enumerate().map(move |(i, f)| f(Key::ElementKey::from((key, i)))))
        };

        let data = self.internal_data();
        for value in values_computed {
            data.push(value);
        }
        key
    }

    /// Create a sequence of values inside the store from an iterator-like
    /// object, returning its key.
    fn create_from_iter(&self, values: impl IntoIterator<Item = Value>) -> Key {
        let data = self.internal_data();
        let starting_index = data.len();
        for value in values {
            data.push(value);
        }
        Key::from_index_and_len_unchecked(starting_index, data.len() - starting_index)
    }

    /// Get the value at the given index in the value sequence corresponding to
    /// the given key.
    ///
    /// Panics if the index is out of bounds for the given key.
    fn get_at_index(&self, key: Key, index: usize) -> &Value {
        let (starting_index, len) = key.to_index_and_len();
        assert!(index < len);
        &self.internal_data()[starting_index + index]
    }
}

/// A default implementation of [`DefaultSequenceAppendOnlyStore`].
pub struct DefaultSequenceAppendOnlyStore<K, V> {
    data: AppendOnlyVec<V>,
    _phantom: PhantomData<K>,
}

impl<K, V> Default for DefaultSequenceAppendOnlyStore<K, V> {
    fn default() -> Self {
        Self { data: AppendOnlyVec::new(), _phantom: PhantomData }
    }
}

impl<K, V> DefaultSequenceAppendOnlyStore<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: SequenceStoreKey, V: Copy> SequenceAppendOnlyStore<K, V>
    for DefaultSequenceAppendOnlyStore<K, V>
{
    fn internal_data(&self) -> &AppendOnlyVec<V> {
        &self.data
    }
}

#[cfg(test)]
mod test_super {
    use super::*;
    // Ensuring macros expand correctly:
    new_store_key!(pub TestK);
    new_sequence_store_key_direct!(pub TestSeqK, TestKK);
}
