use crate::Wall;
use core::fmt;
use std::{
    borrow::Borrow,
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

    pub fn move_out(self) -> T {
        let no_drop_self = ManuallyDrop::new(self);
        // Safety: this value will never be used again (and no destructors will run), so it is safe
        // to bitwise copy out of the castle.
        //
        // @@Todo: verify this
        unsafe { 
            ManuallyDrop::into_inner(std::ptr::read(no_drop_self.data as *const ManuallyDrop<T>))
        }
    }
}

impl<'c, T: Clone> Brick<'c, T> {
    pub fn clone_out(&self) -> T {
        (*self).clone()
    }

    pub fn clone_in<'cc>(&self, wall: &Wall<'cc>) -> Brick<'cc, T> {
        Brick::new(self.clone_out(), wall)
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

impl<T> AsRef<T> for Brick<'_, T> {
    fn as_ref(&self) -> &T {
        self.deref()
    }
}

impl<T> Borrow<T> for Brick<'_, T> {
    fn borrow(&self) -> &T {
        self.deref()
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
