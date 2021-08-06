use crate::Wall;
use core::fmt;
use std::{
    mem::{ManuallyDrop, MaybeUninit},
    ops::{Deref, DerefMut},
};

pub struct Row<'c, T> {
    data: &'c mut [MaybeUninit<ManuallyDrop<T>>],
    length: usize,
}

const ROW_INITIAL_REALLOC_SIZE: usize = 4;
const ROW_REALLOC_MULTIPLIER: usize = 2;

impl<'c, T> Row<'c, T> {
    pub fn new(wall: &Wall<'c>) -> Self {
        Self::with_capacity(0, wall)
    }

    pub fn with_capacity(initial_capacity: usize, wall: &Wall<'c>) -> Self {
        Self {
            data: wall.alloc_uninit_slice(initial_capacity),
            length: 0,
        }
    }

    pub fn capacity(&self) -> usize {
        self.data.len()
    }

    pub fn reserve(&mut self, new_capacity: usize, wall: &Wall<'c>) {
        if new_capacity < self.len() {
            panic!("Tried to reallocate with a capacity smaller than length");
        }

        if new_capacity < self.capacity() {
            // no-op
            return;
        }

        let new_data = wall.alloc_uninit_slice(new_capacity);

        // Safety: Both ranges are valid because they originate from wall.alloc_raw.
        // NB: self.data is now invalid, elements have been moved.
        unsafe {
            std::ptr::copy_nonoverlapping(self.data.as_ptr(), new_data.as_mut_ptr(), self.len());
        }

        self.data = new_data;
    }

    pub fn push(&mut self, element: T, wall: &Wall<'c>) {
        if self.capacity() < self.len() + 1 {
            if self.capacity() == 0 {
                self.reserve(ROW_INITIAL_REALLOC_SIZE, wall);
            } else {
                let new_capacity = self.capacity() * ROW_REALLOC_MULTIPLIER;
                if new_capacity > isize::MAX as usize {
                    panic!("Reallocation target capacity is too large");
                }

                self.reserve(new_capacity, wall);
            }
        }

        // Safety: we just reserved enough for this to be valid.
        *unsafe { self.data.get_unchecked_mut(self.len()) } =
            MaybeUninit::new(ManuallyDrop::new(element));
        self.length += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len() == 0 {
            return None;
        }

        let last_element = std::mem::replace(
            // Safety: @@TODO
            unsafe { self.data.get_unchecked_mut(self.len() - 1) },
            MaybeUninit::uninit(),
        );
        self.length -= 1;

        // Safety: value has beem initialised.
        //
        // We give responsibility of dropping to the caller.
        Some(ManuallyDrop::into_inner(unsafe {
            last_element.assume_init()
        }))
    }

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

    pub fn as_slice(&self) -> &'c [T] {
        // Safety: values until self.length are initialised.
        // Also, the slice will live as long as 'c, which might outlive self.
        unsafe {
            std::mem::transmute::<&[MaybeUninit<ManuallyDrop<T>>], &[T]>(&self.data[0..self.length])
        }
    }
}

#[macro_export]
macro_rules! row {
    ($wall:expr) => {
        $crate::collections::row::Row::new($wall)
    };
    ($wall:expr; $($item:expr),*) => {
        $crate::collections::row::Row::from_iter([$($item,)*], $wall)
    };
    ($wall:expr; $($item:expr,)*) => {
        $crate::collections::row::Row::from_iter([$($item,)*], $wall)
    };
    ($wall:expr; $item:expr; $count:expr) => {
        $crate::collections::row::Row::from_iter(std::iter::repeat($item).take($count), $wall)
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
        self.as_slice()
    }
}

impl<T> DerefMut for Row<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Safety: values until self.length are initialised.
        // Cast from ManuallyDrop is safe because user can't drop through a reference.
        unsafe {
            std::mem::transmute::<&mut [MaybeUninit<ManuallyDrop<T>>], &mut [T]>(
                &mut self.data[0..self.length],
            )
        }
    }
}

impl<T> Drop for Row<'_, T> {
    fn drop(&mut self) {
        // Safety: values until self.length are initialised, and ManuallyDrop<T> has the same layout as T.
        let data_to_drop = unsafe {
            std::mem::transmute::<&mut [MaybeUninit<ManuallyDrop<T>>], &mut ManuallyDrop<[T]>>(
                &mut self.data[0..self.length],
            )
        };

        // Safety: will never be accessed again.
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

impl<'c, T: Clone> Row<'c, T> {
    pub fn clone_out(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    pub fn clone_in<'cc>(&self, wall: &Wall<'cc>) -> Row<'cc, T> {
        Row::from_iter(self.iter().cloned(), wall)
    }
}

#[cfg(test)]
mod tests {
    use crate::{collections::row::Row, Castle};
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn row_construction_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        let row = Row::<i32>::new(&wall);
        assert_eq!(row.capacity(), 0);

        let capacity = 10;
        let row = Row::<i32>::with_capacity(capacity, &wall);
        assert_eq!(row.capacity(), capacity);
    }

    #[test]
    fn row_capacity_test() {
        let castle = Castle::new();
        let wall = castle.wall();

        let mut row = Row::<i32>::new(&wall);
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

        let mut row = Row::<i32>::new(&wall);

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
}
