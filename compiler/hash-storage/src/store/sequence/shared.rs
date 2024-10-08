use std::marker::PhantomData;

use parking_lot::{
    MappedRwLockReadGuard, MappedRwLockWriteGuard, RwLock, RwLockReadGuard, RwLockWriteGuard,
};

use super::SequenceStoreKey;

/// The internal data of a store.
pub type SequenceStoreInternalData<Value> = RwLock<Vec<Value>>;
pub type SequenceStoreBorrowHandle<'a, Value> = MappedRwLockReadGuard<'a, Value>;
pub type SequenceStoreBorrowMutHandle<'a, Value> = MappedRwLockWriteGuard<'a, Value>;

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
        unsafe { Key::from_raw_parts(starting_index, values.len()) }
    }

    /// Create an empty sequence of values inside the store, returning its key.
    fn create_empty(&self) -> Key {
        let starting_index = self.internal_data().read().len();
        unsafe { Key::from_raw_parts(starting_index, 0) }
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
        unsafe { Key::from_raw_parts(starting_index, data.len() - starting_index) }
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
        debug_assert!(index < len);

        unsafe { self.internal_data().read().get_unchecked(starting_index + index).clone() }
    }

    /// Get the value sequence for the given key as an owned vector.
    fn get_vec(&self, key: Key) -> Vec<Value> {
        let (index, len) = key.to_index_and_len();
        self.internal_data().read()[index..index + len].to_vec()
    }

    /// Set the value at the given index in the value sequence corresponding to
    /// the given key, to the given value. Returns the original value.
    ///
    /// Panics if the index is out of bounds for the given key.
    fn set_at_index(&self, key: Key, index: usize, new_value: Value) -> Value {
        let (starting_index, len) = key.to_index_and_len();
        debug_assert!(index < len);

        let mut data = self.internal_data().write();
        let value_ref = unsafe { data.get_unchecked_mut(starting_index + index) };
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
        let value_slice_ref = unsafe { data.get_unchecked_mut(key.to_index_range()) };
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
        let value = unsafe { data.get_unchecked(index..index + len) };
        f(value)
    }

    /// Borrow a value sequence mutably, given a key. Returns an appropriate
    /// handle which implements `DerefMut` to the value slice.
    fn borrow_mut(&self, key: Key) -> SequenceStoreBorrowMutHandle<'_, [Value]> {
        let (index, len) = key.to_index_and_len();
        let data = self.internal_data().write();
        RwLockWriteGuard::map(data, |d| unsafe { d.get_unchecked_mut(index..index + len) })
    }

    /// Borrow a value sequence, given a key. Returns an appropriate handle
    /// which implements `Deref` to the value slice.
    fn borrow(&self, key: Key) -> SequenceStoreBorrowHandle<'_, [Value]> {
        let (index, len) = key.to_index_and_len();
        let data = self.internal_data().read();
        RwLockReadGuard::map(data, |d| unsafe { d.get_unchecked(index..index + len) })
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
        let value = unsafe { data.get_unchecked_mut(index..index + len) };
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
        let value_slice_ref = unsafe { data.get_unchecked_mut(index..index + len) };
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
    type Iter<'s>
        = impl Iterator<Item = Value> + 's
    where
        T: 's,
        Key: 's;
    fn iter(&self, key: Key) -> Self::Iter<'_> {
        unsafe {
            key.to_index_range().map(move |index| {
                self.internal_data().read().get_unchecked(key.entry_index() + index).clone()
            })
        }
    }
}

pub trait TrivialKeySequenceStore<Key: SequenceStoreKey, Value: Clone>:
    SequenceStore<Key, Value>
{
    /// Same as [`SequenceStore::get_at_index`] but takes the element key and
    /// index as a tuple.
    fn get_element(&self, element_id: Key::ElementKey) -> Value;

    /// Borrow a value, given a key. Returns an appropriate handle
    /// which implements `Deref` to the value.
    fn borrow_element(&self, element_id: Key::ElementKey) -> SequenceStoreBorrowHandle<'_, Value>;

    /// Borrow a value mutably, given a key. Returns an appropriate
    /// handle which implements `DerefMut` to the value.
    fn borrow_element_mut(
        &self,
        element_id: Key::ElementKey,
    ) -> SequenceStoreBorrowMutHandle<'_, Value>;
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

    fn borrow_element(&self, element_id: Key::ElementKey) -> SequenceStoreBorrowHandle<'_, Value> {
        let (key, index) = element_id.into();
        let (starting_index, _) = key.to_index_and_len();
        let data = self.internal_data().read();
        RwLockReadGuard::map(data, |d| unsafe { d.get_unchecked(starting_index + index) })
    }

    fn borrow_element_mut(
        &self,
        element_id: Key::ElementKey,
    ) -> SequenceStoreBorrowMutHandle<'_, Value> {
        let (key, index) = element_id.into();
        let (starting_index, _) = key.to_index_and_len();
        let data = self.internal_data().write();
        RwLockWriteGuard::map(data, |d| unsafe { d.get_unchecked_mut(starting_index + index) })
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
