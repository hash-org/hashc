//! Defines a [SequenceStore] and [SequenceStoreKey] for a given type. Such a
//! store keeps a sequence of elements per entry, this is useful for interning
//! a list of items as a single id.

use std::{
    iter::{repeat, Map, Repeat, Zip},
    ops::Range,
};

pub mod local;
pub mod shared;

pub use local::*;
pub use shared::*;

pub type SequenceStoreKeyIter<T, K> = Map<Zip<Repeat<T>, Range<usize>>, fn((T, usize)) -> K>;

/// Represents a key that can be used to index a [`SequenceStore`].
pub trait SequenceStoreKey: Copy + Eq {
    type ElementKey: Copy + Eq;

    /// Turn the key into an index and a length.
    fn to_index_and_len(self) -> (usize, usize);

    /// Create a key from an index and a length.
    ///
    /// # Safety
    /// - This will create a [SequenceStoreKey] without checking the boundaries
    ///   in the [SequenceStore].
    /// - This should generally not be used in client code.
    unsafe fn from_raw_parts(index: usize, len: usize) -> Self;

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
        unsafe { Self::from_raw_parts(0, 0) }
    }
}

pub trait TrivialSequenceStoreKey: SequenceStoreKey {
    type Iter: Iterator<Item = Self::ElementKey>;
    /// Turn the key into a range `(key, 0)..(key, len)`.
    fn iter(self) -> Self::Iter;

    /// Get the key corresponding to the given index.
    fn at(self, index: usize) -> Option<Self::ElementKey>;
}

impl<T: SequenceStoreKey> TrivialSequenceStoreKey for T
where
    T::ElementKey: From<(T, usize)>,
{
    type Iter = SequenceStoreKeyIter<T, T::ElementKey>;
    fn iter(self) -> Self::Iter {
        repeat(self).zip(self.to_index_range()).map(Self::ElementKey::from)
    }

    fn at(self, index: usize) -> Option<Self::ElementKey> {
        if index < self.len() {
            Some(Self::ElementKey::from((self, index)))
        } else {
            None
        }
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

            unsafe fn from_raw_parts(index: usize, len: usize) -> Self {
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
        $visibility struct $el_name(pub $name, pub u32);

        impl $el_name {
            pub fn new(a: $name, b: usize) -> Self {
                Self(a, b as u32)
            }
        }

        impl From<$el_name> for ($name, usize) {
            fn from(value: $el_name) -> Self {
                (value.0, value.1 as usize)
            }
        }

        impl From<($name, usize)> for $el_name {
            fn from(value: ($name, usize)) -> Self {
                Self(value.0, value.1 as u32)
            }
        }

        impl $crate::store::sequence::SequenceStoreKey for $name {
            type ElementKey = $el_name;

            fn to_index_and_len(self) -> (usize, usize) {
                (self.index.try_into().unwrap(), self.len.try_into().unwrap())
            }

            unsafe fn from_raw_parts(index: usize, len: usize) -> Self {
                Self { index: index.try_into().unwrap(), len: len.try_into().unwrap() }
            }
        }
    };
}

#[cfg(test)]
mod test_super {
    // Ensuring macros expand correctly:
    new_sequence_store_key_direct!(pub TestSeqK, TestKK);
}
