use std::marker::PhantomData;

use super::SequenceStoreKey;

/// An implementation of [SequenceStore] which doesn't require being shared
/// across thread boundaries.
pub struct LocalSequenceStore<Key, V> {
    data: Vec<V>,
    _phantom: PhantomData<Key>,
}

impl<Key, V> Default for LocalSequenceStore<Key, V> {
    fn default() -> Self {
        Self { data: Vec::new(), _phantom: PhantomData }
    }
}

impl<Key: SequenceStoreKey, V: Clone> LocalSequenceStore<Key, V> {
    pub fn new() -> Self {
        Self { data: Vec::new(), _phantom: PhantomData }
    }

    /// Create a sequence of values inside the store from a slice, returning its
    /// key.
    pub fn create_from_slice(&mut self, values: &[V]) -> Key {
        let starting_index = self.data.len();
        self.data.extend_from_slice(values);
        unsafe { Key::from_raw_parts(starting_index, values.len()) }
    }

    /// Create an empty sequence of values inside the store, returning its key.
    pub fn create_empty(&self) -> Key {
        unsafe { Key::from_raw_parts(self.data.len(), 0) }
    }

    /// Create a sequence of values inside the store from an iterator-like
    /// object, returning its key.
    ///
    /// *Warning*: Do not call mutating store methods (`create_*` etc) in the
    /// `values` iterator, otherwise there will be a panic. If you want to
    /// do this, consider using [`Self::create_from_iter()`] instead.
    pub fn create_from_iter(&mut self, values: impl IntoIterator<Item = V>) -> Key {
        let starting_index = self.data.len();
        self.data.extend(values);
        unsafe { Key::from_raw_parts(starting_index, self.data.len() - starting_index) }
    }

    /// Get the value sequence for the given key as an owned vector.
    pub fn get_vec(&self, key: Key) -> Vec<V> {
        let (index, len) = key.to_index_and_len();
        self.data[index..index + len].to_vec()
    }

    /// Borrow a collection of items.
    pub fn borrow(&self, key: Key) -> &[V] {
        let (index, len) = key.to_index_and_len();
        &self.data[index..index + len]
    }

    /// Borrow a mutable collection of items.
    pub fn borrow_mut(&mut self, key: Key) -> &mut [V] {
        let (index, len) = key.to_index_and_len();
        &mut self.data[index..index + len]
    }

    pub fn modify<T>(&mut self, key: Key, f: impl FnOnce(&mut [V]) -> T) -> T {
        let (index, len) = key.to_index_and_len();
        let value = unsafe { self.data.get_unchecked_mut(index..index + len) };
        f(value)
    }
}
