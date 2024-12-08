//! Contains a [`Vec`]-like implementation for allocating contiguous sequences
//! within a [`Wall`].

use core::fmt;
use std::{
    borrow::{Borrow, BorrowMut},
    mem::{ManuallyDrop, MaybeUninit},
    ops::{Deref, DerefMut},
};

use super::Wall;

/// A [`Vec`]-like implementation for allocating contiguous sequences within a
/// [`Wall`].
///
/// This is generic over the castle `'c` lifetime, and implements
/// `Deref<Target=T>`.
///
/// It should mostly be used in the same way as [`Vec`].
///
/// Note: Reallocations require copying the data every time, as opposed to
/// [`Vec`] (which calls `realloc`, which in turn might grow the memory block
/// without extra copying). This means that reserving space is even more
/// important when using `Row` than when using [`Vec`].
pub struct Row<'c, T> {
    data: &'c mut [MaybeUninit<ManuallyDrop<T>>],
    length: usize,
}

impl<T> Default for Row<'_, T> {
    fn default() -> Self {
        Self::new()
    }
}

/// How much to initially reserve in the row.
const ROW_INITIAL_REALLOC_SIZE: usize = 4;

/// How much to multiply (.0) and divide (.1) the current capacity by when
/// reallocating.
const ROW_REALLOC_MULT_DIV: (usize, usize) = (2, 1);

impl<'c, T> Row<'c, T> {
    /// Create a new [`Row`] with zero length and capacity.
    pub fn new() -> Self {
        Self { data: &mut [], length: 0 }
    }

    /// Create a new `Row` within the given [`Wall`] with zero length and a
    /// given capacity.
    pub fn with_capacity(initial_capacity: usize, wall: &Wall<'c>) -> Self {
        Self { data: wall.alloc_uninit_slice(initial_capacity), length: 0 }
    }

    /// Get the current capacity of the `Row`.
    pub fn capacity(&self) -> usize {
        self.data.len()
    }

    /// Reserve some capacity within the `Row` by reallocating inside the given
    /// [`Wall`].
    ///
    /// # Panics
    ///
    /// - Panics if `new_capacity` is greater than [`isize::MAX`].
    /// - Panics if `new_capacity` is less than the current length of the `Row`.
    pub fn reserve(&mut self, new_capacity: usize, wall: &Wall<'c>) {
        assert!(new_capacity <= isize::MAX as usize, "Reallocation target capacity is too large");

        assert!(
            new_capacity >= self.len(),
            "Tried to reallocate with a capacity smaller than length"
        );

        if new_capacity < self.capacity() {
            // no-op, already have enough capacity.
            return;
        }

        let new_data = wall.alloc_uninit_slice(new_capacity);

        // ##Safety: Both ranges are valid because they originate from wall.alloc_raw.
        // NB: self.data is now invalid, elements have been moved.
        unsafe {
            std::ptr::copy_nonoverlapping(self.data.as_ptr(), new_data.as_mut_ptr(), self.len());
        }

        self.data = new_data;
    }

    /// Push an element to the end of the `Row`.
    ///
    /// This will reallocate the data inside the given [`Wall`] if there is not
    /// enough capacity to add the element.
    ///
    /// # Panics
    ///
    /// See [`Row::reserve`].
    pub fn push(&mut self, element: T, wall: &Wall<'c>) {
        if self.capacity() < self.len() + 1 {
            if self.capacity() == 0 {
                self.reserve(ROW_INITIAL_REALLOC_SIZE, wall);
            } else {
                let new_capacity =
                    (self.capacity() * ROW_REALLOC_MULT_DIV.0) / ROW_REALLOC_MULT_DIV.1;
                self.reserve(new_capacity, wall);
            }
        }

        // ##Safety: we just reserved enough for this to be valid.
        *unsafe { self.data.get_unchecked_mut(self.len()) } =
            MaybeUninit::new(ManuallyDrop::new(element));
        self.length += 1;
    }

    // pub fn extend(&mut self, elements: Row<T>, wall: &Wall<'c>) {
    //     if self.capacity() < self.len() + elements.len() {
    //     }
    // }

    /// Pop an element from the end of the `Row`
    ///
    /// Returns `None` if there are no elements in the `Row`, otherwise the
    /// popped element.
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        let last_element = std::mem::replace(
            // ##Safety: self.len() - 1 is always a valid index as long as self.len() != 0 (which
            // has just been checked).
            unsafe { self.data.get_unchecked_mut(self.len() - 1) },
            MaybeUninit::uninit(),
        );
        self.length -= 1;

        // ##Safety: value has been initialised because it was within (0..self.len()).
        //
        // We give responsibility of dropping to the caller.
        Some(ManuallyDrop::into_inner(unsafe { last_element.assume_init() }))
    }

    /// Insert an element at a given index inside the `Row`.
    ///
    /// # Panics
    ///
    /// If index is not within the range `(0..=self.len())`. Also see
    /// [`Row::reserve`].
    pub fn insert(&mut self, index: usize, element: T, wall: &Wall<'c>) {
        // Insert at the end means push.
        if index == self.len() {
            return self.push(element, wall);
        }

        assert!(
            (0..self.len()).contains(&index),
            "Out of bounds index when inserting an element into Row"
        );

        // Reserve one more element
        self.reserve(self.len() + 1, wall);

        // Shift elements after insertion point by 1.
        let current_point = &self.data[index] as *const _;
        let target_point = &mut self.data[index + 1] as *mut _;
        let shift_length = self.len() - index;

        // ##Safety: We have reserved one more element than the length so the shift is
        // valid.
        unsafe {
            std::ptr::copy(current_point, target_point, shift_length);
        }

        // Set the element
        self.data[index] = MaybeUninit::new(ManuallyDrop::new(element));

        // Increment the length
        self.length += 1;
    }

    /// Construct a [Row] from an iterator, allocating inside the given
    /// [`Wall`].
    ///
    /// This uses `Iterator::size_hint` to predict how many elements are inside
    /// the iterator, and avoid extraneous reallocations.
    pub fn from_iter<I>(iter: I, wall: &Wall<'c>) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let iter = iter.into_iter();
        let (min_bound, max_bound) = iter.size_hint();
        let initial_capacity = max_bound.unwrap_or(min_bound);

        let mut row = Row::with_capacity(initial_capacity, wall);
        for element in iter {
            row.push(element, wall);
        }

        row
    }

    /// Create a new [Row] from a [`Vec<T>`].
    pub fn from_vec(vec: Vec<T>, wall: &Wall<'c>) -> Self {
        Self::from_iter(vec, wall)
    }

    /// Construct a `Row` from an iterator of [`Result`]s, allocating inside the
    /// given [`Wall`].
    ///
    /// Returns a `Result` of either the collected `Row` or the first error
    /// encountered in the iterator.
    ///
    /// This uses `Iterator::size_hint` to predict how many elements are inside
    /// the iterator, and avoid extraneous reallocations.
    pub fn try_from_iter<I, E>(iter: I, wall: &Wall<'c>) -> Result<Self, E>
    where
        I: IntoIterator<Item = Result<T, E>>,
    {
        let iter = iter.into_iter();
        let (min_bound, max_bound) = iter.size_hint();
        let initial_capacity = max_bound.unwrap_or(min_bound);

        let mut row = Row::with_capacity(initial_capacity, wall);
        for element in iter {
            row.push(element?, wall);
        }

        Ok(row)
    }

    /// Produce a reference to the data inside the `Row` as a mutable slice,
    /// consuming `self`.
    pub fn into_slice(self) -> &'c mut [T] {
        // ##Safety: values until self.length are initialised.
        // Also, the slice will live as long as 'c, which might outlive self.
        unsafe {
            std::mem::transmute::<&mut [MaybeUninit<ManuallyDrop<T>>], &mut [T]>(
                &mut self.data[0..self.length],
            )
        }
    }
}

impl<T: Clone> Row<'_, T> {
    /// Clone the data inside `self` into a [`Vec`].
    pub fn clone_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    /// Clone the data inside `self` into a [`Row`] allocated using the given
    /// [`Wall`].
    pub fn clone_in<'cc>(&self, wall: &Wall<'cc>) -> Row<'cc, T> {
        Row::from_iter(self.iter().cloned(), wall)
    }
}

/// A macro to help in the creation of [`Row`] objects. Similar to the [`vec!`]
/// macro.
///
/// Usage is the same as `vec!`, but with an explicit argument providing the
/// [`Wall`] to allocate into.
///
/// # Examples
///
/// ```
/// use hash_storage::{arena::{Castle, Wall}, row};
/// let castle = Castle::new();
/// let wall = castle.wall();
///
/// let r = row![&wall; 1, 2, 3];
/// assert_eq!(r.as_ref(), &[1, 2, 3]);
///
/// let r = row![&wall; 1; 5];
/// assert_eq!(r.as_ref(), &[1, 1, 1, 1, 1]);
/// ```
#[macro_export]
macro_rules! row {
    () => {
        $crate::arena::row::Row::new()
    };
    ($wall:expr) => {
        $crate::arena::row::Row::new()
    };
    ($wall:expr; $($item:expr),*) => {
        $crate::arena::row::Row::from_iter([$($item,)*], $wall)
    };
    ($wall:expr; $($item:expr,)*) => {
        $crate::arena::row::Row::from_iter([$($item,)*], $wall)
    };
    ($wall:expr; $item:expr; $count:expr) => {
        $crate::arena::row::Row::from_iter(std::iter::repeat($item).take($count), $wall)
    };
}

impl<T: fmt::Debug> fmt::Debug for Row<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T> Deref for Row<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // ##Safety: values until self.length are initialised.
        // Also, the slice will live as long as 'c, which might outlive self.
        unsafe {
            std::mem::transmute::<&[MaybeUninit<ManuallyDrop<T>>], &[T]>(&self.data[0..self.length])
        }
    }
}

impl<T> DerefMut for Row<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // ##Safety: values until self.length are initialised.
        // Cast from ManuallyDrop is safe because user can't drop through a reference.
        unsafe {
            std::mem::transmute::<&mut [MaybeUninit<ManuallyDrop<T>>], &mut [T]>(
                &mut self.data[0..self.length],
            )
        }
    }
}

impl<T> AsRef<[T]> for Row<'_, T> {
    fn as_ref(&self) -> &[T] {
        self.deref()
    }
}

impl<T> AsMut<[T]> for Row<'_, T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.deref_mut()
    }
}

impl<T> Borrow<[T]> for Row<'_, T> {
    fn borrow(&self) -> &[T] {
        self.deref()
    }
}

impl<T> BorrowMut<[T]> for Row<'_, T> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self.deref_mut()
    }
}

impl<'r, T> IntoIterator for &'r Row<'_, T> {
    type Item = &'r T;
    type IntoIter = std::slice::Iter<'r, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.deref().iter()
    }
}

impl<'r, T> IntoIterator for &'r mut Row<'_, T> {
    type Item = &'r mut T;
    type IntoIter = std::slice::IterMut<'r, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.deref_mut().iter_mut()
    }
}

impl<T> Drop for Row<'_, T> {
    fn drop(&mut self) {
        // ##Safety: values until self.length are initialised, and ManuallyDrop<T> has
        // the same layout as T.
        let data_to_drop = unsafe {
            std::mem::transmute::<&mut [MaybeUninit<ManuallyDrop<T>>], &mut ManuallyDrop<[T]>>(
                &mut self.data[0..self.length],
            )
        };

        // ##Safety: will never be accessed again.
        unsafe {
            ManuallyDrop::drop(data_to_drop);
        }
    }
}

impl<T: PartialEq> PartialEq for Row<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl<T: Eq> Eq for Row<'_, T> {}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use crate::arena::{row::Row, Castle};

    #[test]
    fn row_construction_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        let row = Row::<i32>::new();
        assert_eq!(row.capacity(), 0);

        let capacity = 10;
        let row = Row::<i32>::with_capacity(capacity, &wall);
        assert_eq!(row.capacity(), capacity);
    }

    #[test]
    fn row_capacity_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        let mut row = Row::<i32>::new();
        assert_eq!(row.capacity(), 0);

        row.reserve(10, &wall);
        assert_eq!(row.capacity(), 10);

        row.reserve(20, &wall);
        assert_eq!(row.capacity(), 20);

        row.reserve(10, &wall);
        assert_eq!(row.capacity(), 20);
    }

    #[test]
    fn row_push_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        let mut row = Row::<i32>::new();

        // Empty
        assert_eq!(row.as_ref(), &[]);

        // One element
        row.push(1, &wall);
        assert_eq!(row.as_ref(), &[1]);

        // More elements
        row.push(1, &wall);
        row.push(2, &wall);
        row.push(3, &wall);
        assert_eq!(row.as_ref(), &[1, 1, 2, 3]);

        // Popping then pushing
        let el = row.pop();
        row.push(4, &wall);
        assert_eq!(el, Some(3));
        assert_eq!(row.as_ref(), &[1, 1, 2, 4]);
    }

    #[test]
    fn row_drop_test() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug, Clone)]
        struct Foo;
        impl Drop for Foo {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        let castle = Castle::new();
        let wall = castle.wall();

        let foo_count = 100;
        let mut row = Row::from_iter((0..foo_count).map(|_| Foo), &wall);

        // Zero initially
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 0);

        // .pop() doesn't drop
        let el = row.pop();
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 0);

        // Dropping el calls drop.
        drop(el);
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 1);

        // Dropping the row calls drop on the rest.
        drop(row);
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), foo_count);
    }

    #[test]
    fn row_insert_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        let mut r = row![&wall; 1, 2, 3, 5];
        assert_eq!(r.len(), 4);
        r.insert(3, 4, &wall);
        assert_eq!(r.len(), 5);
        assert_eq!(r.as_ref(), &[1, 2, 3, 4, 5]);

        let mut r = row![];
        assert_eq!(r.len(), 0);
        r.insert(0, 1, &wall);
        assert_eq!(r.len(), 1);
        assert_eq!(r.as_ref(), &[1]);
    }
}
