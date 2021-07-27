use super::row::Row;
use crate::Wall;
use core::fmt;
use std::borrow::Borrow;
use std::hash::Hash;
use std::ops::Deref;

pub struct BrickString<'c> {
    inner: Row<'c, u8>,
}

impl<'c> BrickString<'c> {
    pub fn new(value: &str, wall: &Wall<'c>) -> Self {
        let mut brick_str = Self::with_capacity(value.len(), wall);
        for v in value.bytes() {
            brick_str.inner.push(v, wall);
        }
        brick_str
    }

    pub fn with_capacity(initial_capacity: usize, wall: &Wall<'c>) -> Self {
        Self {
            inner: Row::with_capacity(initial_capacity, wall),
        }
    }

    pub fn reserve(&mut self, new_capacity: usize, wall: &Wall<'c>) {
        self.inner.reserve(new_capacity, wall)
    }

    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    pub fn as_str(&self) -> &'c str {
        unsafe { std::str::from_utf8_unchecked(self.inner.as_slice()) }
    }
}

impl Deref for BrickString<'_> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        unsafe { std::str::from_utf8_unchecked(self.inner.deref()) }
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
