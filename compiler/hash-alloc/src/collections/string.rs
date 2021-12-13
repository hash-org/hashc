//! Contains a [`String`]-like implementation for allocating strings within a [`Wall`].
//!
//! All rights reserved 2021 (c) The Hash Language authors

use super::row::Row;
use crate::Wall;
use core::fmt;
use std::borrow::Borrow;
use std::hash::Hash;
use std::ops::Deref;

/// A [`String`]-like implementation for allocating strings within a [`Wall`].
///
/// This is generic over the castle `'c` lifetime, and implements `Deref<Target=str>`.
///
/// It should mostly be used in the same way as [`String`], and uses a `Row<u8>` internally.
pub struct BrickString<'c> {
    inner: Row<'c, u8>,
}

impl<'c> BrickString<'c> {
    /// Create a new `BrickString` within the given [`Wall`], copying the given string value.
    pub fn new(value: &str, wall: &Wall<'c>) -> Self {
        let mut brick_str = Self::with_capacity(value.len(), wall);
        for v in value.bytes() {
            brick_str.inner.push(v, wall);
        }
        brick_str
    }

    /// Create an empty `BrickString` within the given [`Wall`] with a given capacity.
    pub fn with_capacity(initial_capacity: usize, wall: &Wall<'c>) -> Self {
        Self {
            inner: Row::with_capacity(initial_capacity, wall),
        }
    }

    /// Get the current capacity of the `Row`.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Reserve some capacity within the `BrickString` by reallocating inside the given [`Wall`].
    ///
    /// # Panics
    ///
    /// See `Row::reserve`.
    pub fn reserve(&mut self, new_capacity: usize, wall: &Wall<'c>) {
        self.inner.reserve(new_capacity, wall)
    }

    /// Produce a string reference to the data inside `self`.
    pub fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(self.inner.as_ref()) }
    }

    /// Produce a string reference to the data inside `self`, consuming self.
    ///
    /// This is valid because the data is stored within the underlying [`crate::Castle`], which can
    /// outlive `Self`.
    pub fn into_str(self) -> &'c str {
        unsafe { std::str::from_utf8_unchecked(self.inner.into_slice()) }
    }
}

impl Deref for BrickString<'_> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl Borrow<str> for BrickString<'_> {
    fn borrow(&self) -> &str {
        self.deref()
    }
}

impl AsRef<str> for BrickString<'_> {
    fn as_ref(&self) -> &str {
        self.deref()
    }
}

impl fmt::Debug for BrickString<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl Hash for BrickString<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
    }
}

impl PartialEq for BrickString<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl Eq for BrickString<'_> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Castle;

    #[test]
    fn brick_string_valid_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        let s = BrickString::new("Hello, world!", &wall);
        assert_eq!(s.as_str(), "Hello, world!");
    }
}
