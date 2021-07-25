use crate::Wall;
use core::fmt;
use std::{
    mem::ManuallyDrop,
    ops::{Deref, DerefMut},
};

pub struct Brick<'c, T> {
    data: &'c mut ManuallyDrop<T>,
}

impl<'c, T> Brick<'c, T> {
    pub fn new(x: T, wall: &Wall<'c>) -> Self {
        Self {
            data: wall.alloc_value(x),
        }
    }
}

impl<'c, T: Clone> Brick<'c, T> {
    pub fn clone_out(&self) -> T {
        (*self).clone()
    }
}

impl<T: PartialEq> PartialEq for Brick<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl<T: Eq> Eq for Brick<'_, T> {}

impl<T> Deref for Brick<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.data
    }
}

impl<T> DerefMut for Brick<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.data
    }
}

impl<T: fmt::Debug> fmt::Debug for Brick<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T> Drop for Brick<'_, T> {
    fn drop(&mut self) {
        // Safety: destructor only runs once.
        unsafe {
            ManuallyDrop::drop(self.data);
        }
    }
}
