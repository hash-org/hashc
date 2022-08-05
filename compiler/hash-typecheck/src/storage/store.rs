//! Provides generic data structures to store values by generated keys in an
//! efficient way, with interior mutability.
use std::{cell::RefCell, hash::Hash, marker::PhantomData, ops::Range};

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
        #[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
        $visibility struct $name {
            index: usize,
        }

        impl $crate::storage::store::StoreKey for $name {
            fn to_index(self) -> usize {
                self.index
            }

            fn from_index_unchecked(index: usize) -> Self {
                Self { index }
            }
        }
    };
}

/// A store, which provides a way to efficiently store values indexed by opaque
/// generated keys.
///
/// Use [`make_store_key`] to make such a key type.
///
/// This data structure has interior mutability and so all of its methods take
/// `&self`. This makes it easy to use from within contexts without having to
/// worry too much about borrowing rules.
///
/// *Warning*: The `Value`'s `Clone` implementation must not interact with the
/// store, otherwise it might lead to a panic.
#[derive(Default, Debug)]
pub struct Store<Key, Value> {
    data: RefCell<Vec<Value>>,
    _key: PhantomData<Key>,
}

impl<Key: StoreKey, Value: Clone> Store<Key, Value> {
    /// Create a new empty store.
    pub fn new() -> Self {
        Self { _key: PhantomData::default(), data: RefCell::new(Vec::new()) }
    }

    /// Create a value inside the store, returning its key.
    pub fn create(&self, value: Value) -> Key {
        let mut data = self.data.borrow_mut();
        let next_index = data.len();
        data.push(value);
        Key::from_index_unchecked(next_index)
    }

    /// Get a value by its key.
    pub fn get(&self, key: Key) -> Value {
        self.data.borrow().get(key.to_index()).unwrap().clone()
    }

    /// Set a key's value to a new value, returning the old value.
    pub fn set(&self, key: Key, new_value: Value) -> Value {
        let mut data = self.data.borrow_mut();
        let value_ref = data.get_mut(key.to_index()).unwrap();
        let old_value = value_ref.clone();
        *value_ref = new_value;
        old_value
    }

    /// Get a value by a key, and map it to another value given its reference.
    ///
    /// *Warning*: Do not call mutating store methods (`create` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`Self::map()`] instead.
    pub fn map_fast<T>(&self, key: Key, f: impl FnOnce(&Value) -> T) -> T {
        let data = self.data.borrow();
        let value = data.get(key.to_index()).unwrap();
        f(value)
    }

    /// Get a value by a key, and map it to another value given its reference.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create` etc). If you do not need to modify the
    /// store, consider using [`Self::map_fast()`] instead.
    pub fn map<T>(&self, key: Key, f: impl FnOnce(&Value) -> T) -> T {
        let value = self.get(key);
        f(&value)
    }

    /// Modify a value by a key, possibly returning another value.
    ///
    /// *Warning*: Do not call mutating store methods (`create` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`Self::modify()`] instead.
    pub fn modify_fast<T>(&self, key: Key, f: impl FnOnce(&mut Value) -> T) -> T {
        let mut data = self.data.borrow_mut();
        let value = data.get_mut(key.to_index()).unwrap();
        f(value)
    }

    /// Modify a value by a key, possibly returning another value.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create` etc). If you do not need to modify the
    /// store, consider using [`Self::modify_fast()`] instead.
    pub fn modify<T>(&self, key: Key, f: impl FnOnce(&mut Value) -> T) -> T {
        let mut value = self.get(key);
        let ret = f(&mut value);
        self.set(key, value);
        ret
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
    fn index(self) -> usize {
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
            index: usize,
            len: usize,
        }

        impl $crate::storage::store::SequenceStoreKey for $name {
            fn to_index_and_len(self) -> (usize, usize) {
                (self.index, self.len)
            }

            fn from_index_and_len_unchecked(index: usize, len: usize) -> Self {
                Self { index, len }
            }
        }
    };
}

/// A sequence store, which provides a way to efficiently store sequences of
/// contiguous values by an opaque generated key.
///
/// Use [`make_sequence_store_key`] to make such a key type.
///
/// Like [`Store`], this data structure has interior mutability and so all of
/// its methods take `&self`. This makes it easy to use from within contexts
/// without having to worry too much about borrowing rules.
///
/// *Warning*: The `Value`'s `Clone` implementation must not interact with the
/// store, otherwise it might lead to a panic.
#[derive(Default, Debug)]
pub struct SequenceStore<Key, Value> {
    data: RefCell<Vec<Value>>,
    _key: PhantomData<Key>,
}

impl<Key: SequenceStoreKey, Value: Clone> SequenceStore<Key, Value> {
    /// Create a new empty store.
    pub fn new() -> Self {
        Self { _key: PhantomData::default(), data: RefCell::new(Vec::new()) }
    }

    /// Create a sequence of values inside the store from a slice, returning its
    /// key.
    pub fn create_from_slice(&self, values: &[Value]) -> Key {
        let mut data = self.data.borrow_mut();
        let starting_index = data.len();
        data.extend_from_slice(values);
        Key::from_index_and_len_unchecked(starting_index, values.len())
    }

    /// Create a sequence of values inside the store from an iterator-like
    /// object, returning its key.
    ///
    /// *Warning*: Do not call mutating store methods (`create_*` etc) in the
    /// `values` iterator, otherwise there will be a panic. If you want to
    /// do this, consider using [`Self::create_from_iter()`] instead.
    pub fn create_from_iter_fast(&self, values: impl IntoIterator<Item = Value>) -> Key {
        let mut data = self.data.borrow_mut();
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
    pub fn create_from_iter(&self, values: impl IntoIterator<Item = Value>) -> Key {
        let values = values.into_iter().collect::<Vec<_>>();
        self.create_from_slice(&values)
    }

    /// Try create a sequence of values inside the store from an iterator-like
    /// object, returning its key, or an error if it occurred.
    ///
    /// *Warning*: Do not call mutating store methods (`create_*` etc) in the
    /// `values` iterator, otherwise there will be a panic. If you want to
    /// do this, consider using [`Self::create_from_iter()`] instead.
    pub fn try_create_from_iter_fast<E>(
        &self,
        values: impl IntoIterator<Item = Result<Value, E>>,
    ) -> Result<Key, E> {
        let mut data = self.data.borrow_mut();
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
    pub fn try_create_from_iter<E>(
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
    pub fn get_at_index(&self, key: Key, index: usize) -> Value {
        let (starting_index, len) = key.to_index_and_len();
        assert!(index < len);
        self.data.borrow().get(starting_index + index).unwrap().clone()
    }

    /// Get the value sequence for the given key as an owned vector.
    pub fn get_vec(&self, key: Key) -> Vec<Value> {
        self.data.borrow().get(key.to_index_range()).unwrap().to_vec()
    }

    /// Set the value at the given index in the value sequence corresponding to
    /// the given key, to the given value. Returns the original value.
    ///
    /// Panics if the index is out of bounds for the given key.
    pub fn set_at_index(&self, key: Key, index: usize, new_value: Value) -> Value {
        let (starting_index, len) = key.to_index_and_len();
        assert!(index < len);
        let mut data = self.data.borrow_mut();
        let value_ref = data.get_mut(starting_index + index).unwrap();
        let old_value = value_ref.clone();
        *value_ref = new_value;
        old_value
    }

    /// Set the value sequence corresponding to the given key, to the given
    /// slice.
    ///
    /// Panics if the slice is not the same size as the existing value.
    pub fn set_from_slice_cloned(&self, key: Key, new_value_sequence: &[Value]) {
        assert!(key.len() == new_value_sequence.len());
        let mut data = self.data.borrow_mut();
        let value_slice_ref = data.get_mut(key.to_index_range()).unwrap();
        value_slice_ref.clone_from_slice(new_value_sequence);
    }

    /// Get a value sequence by a key, and map it to another value given its
    /// slice.
    ///
    /// *Warning*: Do not call mutating store methods (`create_*` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`Self::map()`] instead.
    pub fn map_fast<T>(&self, key: Key, f: impl FnOnce(&[Value]) -> T) -> T {
        let data = self.data.borrow();
        let value = data.get(key.to_index_range()).unwrap();
        f(value)
    }

    /// Get a value sequence by a key, and map it to another value given its
    /// slice.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create_*` etc). If you do not need to modify the
    /// store, consider using [`Self::map_fast()`] instead.
    pub fn map<T>(&self, key: Key, f: impl FnOnce(&[Value]) -> T) -> T {
        let value = self.get_vec(key);
        f(&value)
    }

    /// Modify a value sequence by a key, possibly returning another value.
    ///
    /// *Warning*: Do not call mutating store methods (`create_*` etc) in `f`
    /// otherwise there will be a panic. If you want to do this, consider using
    /// [`Self::modify()`] instead.
    pub fn modify_fast<T>(&self, key: Key, f: impl FnOnce(&mut [Value]) -> T) -> T {
        let mut data = self.data.borrow_mut();
        let value = data.get_mut(key.to_index_range()).unwrap();
        f(value)
    }

    /// Modify a value sequence by a key, possibly returning another value.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create_*` etc). If you do not need to modify the
    /// store, consider using [`Self::modify_fast()`] instead.
    pub fn modify_cloned<T>(&self, key: Key, f: impl FnOnce(&mut [Value]) -> T) -> T {
        let mut value = self.get_vec(key);
        let ret = f(&mut value);
        self.set_from_slice_cloned(key, &value);
        ret
    }
}

impl<Key: SequenceStoreKey, Value: Copy> SequenceStore<Key, Value> {
    /// Set the value sequence corresponding to the given key, to the given
    /// slice. Uses `memcpy` to do this, given that the value implements `Copy`.
    ///
    /// Panics if the slice is not the same size as the existing value.
    pub fn set_from_slice_copied(&self, key: Key, new_value_sequence: &[Value]) {
        assert!(key.len() == new_value_sequence.len());
        let mut data = self.data.borrow_mut();
        let value_slice_ref = data.get_mut(key.to_index_range()).unwrap();
        value_slice_ref.copy_from_slice(new_value_sequence);
    }

    /// Modify a value sequence by a key, possibly returning another value.
    /// Uses `memcpy` to update the original sequence, given that the value
    /// implements `Copy`.
    ///
    /// It is safe to provide a closure `f` to this function that modifies the
    /// store in some way (`create_*` etc). If you do not need to modify the
    /// store, consider using [`Self::modify_fast()`] instead.
    pub fn modify_copied<T>(&self, key: Key, f: impl FnOnce(&mut [Value]) -> T) -> T {
        let mut value = self.get_vec(key);
        let ret = f(&mut value);
        self.set_from_slice_copied(key, &value);
        ret
    }
}
