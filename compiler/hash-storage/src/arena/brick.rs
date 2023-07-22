//! Contains a [`Box`]-like implementation for allocating values within a
//! [`Wall`].

use core::fmt;
use std::{
    borrow::{Borrow, BorrowMut},
    mem::ManuallyDrop,
    ops::{Deref, DerefMut},
};

use super::Wall;

/// A [`Box`]-like implementation for allocating values within a [`Wall`].
///
/// This is generic over the castle `'c` lifetime, and implements
/// `Deref<Target=T>`.
///
/// It should mostly be used in the same way as [`Box`], and is a zero-cost
/// abstraction over a pointer into the memory arena.
pub struct Brick<'c, T> {
    data: &'c mut ManuallyDrop<T>,
}

impl<'c, T> Brick<'c, T> {
    /// Create a new `Brick` within the given [`Wall`], containing the given
    /// value.
    pub fn new(value: T, wall: &Wall<'c>) -> Self {
        Self { data: wall.alloc_value(value) }
    }

    /// Move the value inside this `Brick` out, consuming the brick.
    ///
    /// This will always perform a bitwise-copy of the data stored in the arena.
    pub fn move_out(self) -> T {
        let no_drop_self = ManuallyDrop::new(self);
        // ##Safety: this value will never be used again (and no destructors will run),
        // so it is safe to bitwise copy out of the castle.
        //
        // @@Verify: make sure that this is completely valid in all cases.
        unsafe {
            ManuallyDrop::into_inner(std::ptr::read(no_drop_self.data as *const ManuallyDrop<T>))
        }
    }
}

impl<'c, T: Clone> Brick<'c, T> {
    /// Clone the value inside the `Brick`, and return the cloned value itself.
    pub fn clone_out(&self) -> T {
        (*self).clone()
    }

    /// Clone the value inside the `Brick`, and place it inside a new `Brick`.
    ///
    /// The new `Brick` will be allocated inside the given [`Wall`].
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
impl<T> AsMut<T> for Brick<'_, T> {
    fn as_mut(&mut self) -> &mut T {
        self.deref_mut()
    }
}

impl<T> Borrow<T> for Brick<'_, T> {
    fn borrow(&self) -> &T {
        self.deref()
    }
}

impl<T> BorrowMut<T> for Brick<'_, T> {
    fn borrow_mut(&mut self) -> &mut T {
        self.deref_mut()
    }
}

impl<T> Drop for Brick<'_, T> {
    fn drop(&mut self) {
        // ##Safety: destructor only runs once.
        unsafe {
            ManuallyDrop::drop(self.data);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::Castle;

    #[test]
    fn brick_construction_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        let b = Brick::new(42, &wall);
        assert_eq!(*b, 42);
    }

    #[test]
    fn brick_move_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        #[derive(Debug, PartialEq, Eq)]
        struct Foo(i32);

        let b = Brick::new(Foo(12), &wall);

        let f = b.move_out();
        assert_eq!(f, Foo(12));
    }

    #[test]
    fn brick_clone_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        #[derive(Debug, PartialEq, Eq, Clone)]
        struct Bar(char);

        let b = Brick::new(Bar('a'), &wall);

        let b2 = b.clone_out();
        assert_eq!(b2, Bar('a'));

        let b3 = b.clone_in(&wall);
        assert_eq!(*b3, Bar('a'));
    }
}
