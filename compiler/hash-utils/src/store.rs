//! Provides generic data structures to store values by generated keys in an
//! efficient way, with interior mutability.
// @@Organisation: Move this module to the `hash_alloc` crate and split it into
// smaller modules.
use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    hash::Hash,
    marker::PhantomData,
    ops::Range,
};

use append_only_vec::AppendOnlyVec;

/// Represents a key that can be used to index a [`Store`].
pub trait StoreKey: Copy + Eq + Hash {
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
    ($visibility:vis $name:ident) => {
        #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Debug)]
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

/// Create a new [`Store`] with the given name, key and value type.
#[macro_export]
macro_rules! new_store {
    ($visibility:vis $name:ident<$Key:ty, $Value:ty>) => {
        #[derive(Default, Debug)]
        $visibility struct $name {
            data: std::cell::RefCell<Vec<$Value>>,
        }

        #[allow(dead_code)]
        impl $name {
            /// Create a new empty store.
            $visibility fn new() -> Self {
                Self { data: std::cell::RefCell::new(Vec::new()) }
            }
        }

        impl $crate::store::Store<$Key, $Value> for $name {
            fn internal_data(&self) -> &std::cell::RefCell<Vec<$Value>> {
                &self.data
            }
        }
    };
}

/// Create a new [`PartialStore`] with the given name, key and value type.
#[macro_export]
macro_rules! new_partial_store {
    ($visibility:vis $name:ident<$Key:ty, $Value:ty>) => {
        #[derive(Default, Debug)]
        $visibility struct $name {
            data: std::cell::RefCell<std::collections::HashMap<$Key, $Value>>,
        }

        #[allow(dead_code)]
        impl $name {
            /// Create a new empty store.
            $visibility fn new() -> Self {
                Self { data: std::cell::RefCell::new(std::collections::HashMap::new()) }
            }
        }

        impl $crate::store::PartialStore<$Key, $Value> for $name {
            fn internal_data(&self) -> &std::cell::RefCell<std::collections::HashMap<$Key, $Value>> {
                &self.data
            }
        }
    };
}

/// Create a new [`SequenceStore`] with the given name, key and value type.
#[macro_export]
macro_rules! new_sequence_store {
    ($visibility:vis $name:ident<$Key:ty, $Value:ty>) => {
        #[derive(Default, Debug)]
        $visibility struct $name {
            data: std::cell::RefCell<Vec<$Value>>,
        }

        #[allow(dead_code)]
        impl $name {
            /// Create a new empty store.
            $visibility fn new() -> Self {
                Self { data: std::cell::RefCell::new(Vec::new()) }
            }
        }

        impl $crate::store::SequenceStore<$Key, $Value> for $name {
            fn internal_data(&self) -> &std::cell::RefCell<Vec<$Value>> {
                &self.data
            }
        }
    };
}

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
    fn internal_data(&self) -> &RefCell<Vec<Value>>;

    /// Create a value inside the store, given its key, returning its key.
    fn create_with(&self, value_fn: impl FnOnce(Key) -> Value) -> Key {
        let mut data = self.internal_data().borrow_mut();
        let next_index = data.len();
        let key = Key::from_index_unchecked(next_index);
        data.push(value_fn(key));
        key
    }

    /// Create a value inside the store, returning its key.
    fn create(&self, value: Value) -> Key {
        let mut data = self.internal_data().borrow_mut();
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
        let data = self.internal_data().borrow();
        let value = data.get(key.to_index()).unwrap();
        f(value)
    }

    /// Modify a value by a key, possibly returning another value.
    ///
    /// *Warning*: Do not call mutating store methods (`create` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`CloneStore::modify()`] instead.
    fn modify_fast<T>(&self, key: Key, f: impl FnOnce(&mut Value) -> T) -> T {
        let mut data = self.internal_data().borrow_mut();
        let value = data.get_mut(key.to_index()).unwrap();
        f(value)
    }
}

/// Additional functionality for [`Store`] when the value implements [`Clone`].
pub trait CloneStore<Key: StoreKey, Value: Clone>: Store<Key, Value> {
    /// Get a value by its key.
    fn get(&self, key: Key) -> Value {
        self.internal_data().borrow().get(key.to_index()).unwrap().clone()
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
        let mut data = self.internal_data().borrow_mut();
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
    data: RefCell<Vec<V>>,
    _phantom: PhantomData<K>,
}

impl<K, V> std::default::Default for DefaultStore<K, V> {
    fn default() -> Self {
        Self { data: RefCell::new(Vec::new()), _phantom: PhantomData::default() }
    }
}

impl<K, V> DefaultStore<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: StoreKey, V: Clone> Store<K, V> for DefaultStore<K, V> {
    fn internal_data(&self) -> &RefCell<Vec<V>> {
        &self.data
    }
}

/// Represents a key that can be used to index a [`SequenceStore`].
pub trait SequenceStoreKey: Copy + Eq + Hash {
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
}

/// Create a new [`SequenceStoreKey`] with the given name.
#[macro_export]
macro_rules! new_sequence_store_key {
    ($visibility:vis $name:ident) => {
        #[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
        $visibility struct $name {
            index: u32,
            len: u32,
        }

        impl $crate::store::SequenceStoreKey for $name {
            fn to_index_and_len(self) -> (usize, usize) {
                (self.index.try_into().unwrap(), self.len.try_into().unwrap())
            }

            fn from_index_and_len_unchecked(index: usize, len: usize) -> Self {
                Self { index: index.try_into().unwrap(), len: len.try_into().unwrap() }
            }
        }
    };
}

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
    fn internal_data(&self) -> &RefCell<Vec<Value>>;

    /// Create a sequence of values inside the store from a slice, returning its
    /// key.
    fn create_from_slice(&self, values: &[Value]) -> Key {
        let mut data = self.internal_data().borrow_mut();
        let starting_index = data.len();
        data.extend_from_slice(values);
        Key::from_index_and_len_unchecked(starting_index, values.len())
    }

    /// Create an empty sequence of values inside the store, returning its key.
    fn create_empty(&self) -> Key {
        let starting_index = self.internal_data().borrow().len();
        Key::from_index_and_len_unchecked(starting_index, 0)
    }

    /// Same as [`SequenceStore::create_from_iter()`], but each value takes its
    /// key and index.
    ///
    /// The given iterator must support [`ExactSizeIterator`].
    fn create_from_iter_with<F: FnOnce((Key, usize)) -> Value, I: IntoIterator<Item = F>>(
        &self,
        values: I,
    ) -> Key
    where
        I::IntoIter: ExactSizeIterator,
    {
        let starting_index = self.internal_data().borrow().len();

        let (key, values_computed) = {
            let values = values.into_iter();
            let key = Key::from_index_and_len_unchecked(starting_index, values.len());
            (key, values.enumerate().map(|(i, f)| f((key, i))).collect::<Vec<_>>())
        };

        let mut data = self.internal_data().borrow_mut();
        data.extend(values_computed.into_iter());
        key
    }

    /// Create a sequence of values inside the store from an iterator-like
    /// object, returning its key.
    ///
    /// *Warning*: Do not call mutating store methods (`create_*` etc) in the
    /// `values` iterator, otherwise there will be a panic. If you want to
    /// do this, consider using [`Self::create_from_iter()`] instead.
    fn create_from_iter_fast(&self, values: impl IntoIterator<Item = Value>) -> Key {
        let mut data = self.internal_data().borrow_mut();
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
        let mut data = self.internal_data().borrow_mut();
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

    /// Same as [`SequenceStore::get_at_index`] but takes the element key and
    /// index as a tuple.
    fn get_element(&self, element_id: (Key, usize)) -> Value {
        self.get_at_index(element_id.0, element_id.1)
    }

    /// Get the value at the given index in the value sequence corresponding to
    /// the given key.
    ///
    /// Panics if the index is out of bounds for the given key.
    fn get_at_index(&self, key: Key, index: usize) -> Value {
        let (starting_index, len) = key.to_index_and_len();
        assert!(index < len);
        self.internal_data().borrow().get(starting_index + index).unwrap().clone()
    }

    /// Get the value sequence for the given key as an owned vector.
    fn get_vec(&self, key: Key) -> Vec<Value> {
        let (index, len) = key.to_index_and_len();
        self.internal_data().borrow().get(index..index + len).unwrap().to_vec()
    }

    /// Set the value at the given index in the value sequence corresponding to
    /// the given key, to the given value. Returns the original value.
    ///
    /// Panics if the index is out of bounds for the given key.
    fn set_at_index(&self, key: Key, index: usize, new_value: Value) -> Value {
        let (starting_index, len) = key.to_index_and_len();
        assert!(index < len);
        let mut data = self.internal_data().borrow_mut();
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
        let mut data = self.internal_data().borrow_mut();
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
        let data = self.internal_data().borrow();
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
        let mut data = self.internal_data().borrow_mut();
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
        let mut data = self.internal_data().borrow_mut();
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
            self.internal_data().borrow().get(key.entry_index() + index).unwrap().clone()
        })
    }
}

/// A default implementation of [`SequenceStore`].
#[derive(Debug)]
pub struct DefaultSequenceStore<K, V> {
    data: RefCell<Vec<V>>,
    _phantom: PhantomData<K>,
}

impl<K, V> std::default::Default for DefaultSequenceStore<K, V> {
    fn default() -> Self {
        Self { data: RefCell::new(Vec::new()), _phantom: PhantomData::default() }
    }
}

impl<K, V> DefaultSequenceStore<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: SequenceStoreKey, V: Clone> SequenceStore<K, V> for DefaultSequenceStore<K, V> {
    fn internal_data(&self) -> &RefCell<Vec<V>> {
        &self.data
    }
}

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
pub trait PartialStore<Key: Copy + Eq + Hash, Value: Clone> {
    fn internal_data(&self) -> &RefCell<HashMap<Key, Value>>;

    /// Insert a key-value pair inside the store, returning the old value if it
    /// exists.
    fn insert(&self, key: Key, value: Value) -> Option<Value> {
        self.internal_data().borrow_mut().insert(key, value)
    }

    /// Get a value by its key, if it exists.
    fn get(&self, key: Key) -> Option<Value> {
        self.internal_data().borrow().get(&key).cloned()
    }

    /// Whether the store has the given key.
    fn has(&self, key: Key) -> bool {
        self.internal_data().borrow().contains_key(&key)
    }

    /// Get a value by a key, and map it to another value given its reference,
    /// if it exists.
    ///
    /// *Warning*: Do not call mutating store methods (`create` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`Self::map()`] instead.
    fn map_fast<T>(&self, key: Key, f: impl FnOnce(Option<&Value>) -> T) -> T {
        let data = self.internal_data().borrow();
        let value = data.get(&key);
        f(value)
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
    /// *Warning*: Do not call mutating store methods (`create` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`Self::modify()`] instead.
    fn modify_fast<T>(&self, key: Key, f: impl FnOnce(Option<&mut Value>) -> T) -> T {
        let mut data = self.internal_data().borrow_mut();
        let value = data.get_mut(&key);
        f(value)
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

    /// The number of entries in the store.
    fn len(&self) -> usize {
        self.internal_data().borrow().len()
    }

    /// Whether the store is empty.
    fn is_empty(&self) -> bool {
        self.internal_data().borrow().is_empty()
    }

    /// Clear the store of all key-value pairs.
    fn clear(&self) {
        self.internal_data().borrow_mut().clear()
    }
}

/// A default implementation of [`PartialStore`].
#[derive(Debug)]
pub struct DefaultPartialStore<K, V> {
    data: std::cell::RefCell<std::collections::HashMap<K, V>>,
}

impl<K, V> std::default::Default for DefaultPartialStore<K, V> {
    fn default() -> Self {
        Self { data: RefCell::new(HashMap::new()) }
    }
}

impl<K, V> DefaultPartialStore<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: Copy + Eq + Hash, V: Clone> PartialStore<K, V> for DefaultPartialStore<K, V> {
    fn internal_data(&self) -> &RefCell<HashMap<K, V>> {
        &self.data
    }
}

#[cfg(test)]
mod test_super {
    use super::*;
    // Ensuring macros expand correctly:
    new_store_key!(pub TestK);
    new_store!(pub Test<TestK, ()>);
    new_sequence_store_key!(pub TestSeqK);
    new_sequence_store!(pub TestSeq<TestSeqK, ()>);
    new_partial_store!(pub TestPartial<TestK, ()>);
}

/// This store uses [`AppendOnlyVec`] internally, rather than a
/// [`RefCell<Vec<_>>`], so that there isn't additional overhead when
/// reading/writing elements; you can take references out of it. The trade-off
/// is that the value needs to implement [`Copy`].
pub trait CellStore<Key: StoreKey, Value: Copy> {
    /// Get a reference to the internal data of the store.
    ///
    /// This should only be used to implement new store methods, not to access
    /// the store.
    fn internal_data(&self) -> &AppendOnlyVec<Cell<Value>>;

    /// Create a value inside the store, given its key, returning its key.
    fn create_with(&self, value_fn: impl FnOnce(Key) -> Value) -> Key {
        let data = self.internal_data();
        let next_index = data.len();
        let key = Key::from_index_unchecked(next_index);
        data.push(Cell::new(value_fn(key)));
        key
    }

    /// Create a value inside the store, returning its key.
    fn create(&self, value: Value) -> Key {
        let data = self.internal_data();
        let next_index = data.len();
        data.push(Cell::new(value));
        Key::from_index_unchecked(next_index)
    }

    /// Get a reference to a value by its key, given that it exists.
    fn get(&self, key: Key) -> &Cell<Value> {
        let data = self.internal_data();
        &data[key.to_index()]
    }
}

/// This is the equivalent to [`CellStore`] but for sequences of values.
///
/// Note that you cannot get slices of values from this store, as the values
/// are not necessarily stored contiguously in memory. You can, however, iterate
/// the sequence store key and read the corresponding value references using
/// [`SequenceCellStore::get_element()`].
pub trait SequenceCellStore<Key: SequenceStoreKey, Value: Copy> {
    /// Get a reference to the internal data of the store.
    ///
    /// This should only be used to implement new store methods, not to access
    /// the store.
    fn internal_data(&self) -> &AppendOnlyVec<Cell<Value>>;

    /// Create a sequence inside the store from the given slice of values,
    /// returning its key.
    fn create_from_slice(&self, values: &[Value]) -> Key {
        let data = self.internal_data();
        let starting_index = data.len();
        for value in values {
            data.push(Cell::new(*value));
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
    fn create_from_iter_with<F: FnOnce((Key, usize)) -> Value, I: IntoIterator<Item = F>>(
        &self,
        values: I,
    ) -> Key
    where
        I::IntoIter: ExactSizeIterator,
    {
        let starting_index = self.internal_data().len();

        let (key, values_computed) = {
            let values = values.into_iter();
            let key = Key::from_index_and_len_unchecked(starting_index, values.len());
            (key, values.enumerate().map(move |(i, f)| f((key, i))))
        };

        let data = self.internal_data();
        for value in values_computed {
            data.push(Cell::new(value));
        }
        key
    }

    /// Create a sequence of values inside the store from an iterator-like
    /// object, returning its key.
    fn create_from_iter(&self, values: impl IntoIterator<Item = Value>) -> Key {
        let data = self.internal_data();
        let starting_index = data.len();
        for value in values {
            data.push(Cell::new(value));
        }
        Key::from_index_and_len_unchecked(starting_index, data.len() - starting_index)
    }

    /// Same as [`SequenceStore::get_at_index`] but takes the element key and
    /// index as a tuple.
    fn get_element(&self, element_id: (Key, usize)) -> &Cell<Value> {
        self.get_at_index(element_id.0, element_id.1)
    }

    /// Get the value at the given index in the value sequence corresponding to
    /// the given key.
    ///
    /// Panics if the index is out of bounds for the given key.
    fn get_at_index(&self, key: Key, index: usize) -> &Cell<Value> {
        let (starting_index, len) = key.to_index_and_len();
        assert!(index < len);
        &self.internal_data()[starting_index + index]
    }
}
