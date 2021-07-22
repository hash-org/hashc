//! Arena allocator implementation for use within the Hash compiler sources.
//!
//! All rights reserved 2021 (c) The Hash Language authors

#![allow(dead_code)] // @@REMOVE
#![feature(bench_black_box)]

use core::fmt;
use parking_lot::Mutex;
use std::{
    alloc::Layout,
    cell::{Cell, UnsafeCell},
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

/// @@TODO: maybe make the ARENA_PAGE_SIZE configurable via 'cfg'?
/// 1MiB
const INITIAL_SECTION_SIZE: usize = 1 << 20;

#[derive(Debug)]
struct WallSection {
    data: Box<[u8]>,
    offset: Cell<usize>,
}

impl Default for WallSection {
    fn default() -> Self {
        WallSection::new(INITIAL_SECTION_SIZE)
    }
}

impl WallSection {
    fn new(capacity: usize) -> Self {
        Self {
            data: vec![0; capacity].into_boxed_slice(),
            offset: Cell::new(0),
        }
    }

    fn alloc(&self, layout: Layout) -> Option<NonNull<u8>> {
        // Old value is start
        let start = {
            let layout_size = layout.size();

            let old_offset = self.offset.get();
            let new_offset = old_offset + layout_size;
            if new_offset >= self.data.len() {
                // We cannot allocate.
                return None;
            }
            self.offset.set(new_offset);

            old_offset
        };

        // Pointer to return is `start` offset from self.data.
        // Safety: we have ensured that the layout fits on the brick.
        let ptr = unsafe {
            NonNull::new_unchecked(self.data.as_ptr().offset(start as isize) as *mut u8)
        };
        Some(ptr)
    }

    fn len(&self) -> usize {
        self.data.len()
    }
}

#[derive(Debug)]
pub struct Wall<'c> {
    curr_section: UnsafeCell<WallSection>,
    past_sections: &'c PastSections,
}

impl<'c> Wall<'c> {
    fn new(past_sections: &'c PastSections) -> Self {
        Self {
            curr_section: UnsafeCell::new(WallSection::default()),
            past_sections,
        }
    }

    fn alloc_raw(&self, layout: Layout) -> NonNull<u8> {
        loop {
            let curr_section = unsafe { &*self.curr_section.get() };
            match curr_section.alloc(layout) {
                Some(result) => {
                    break result;
                }
                None => {
                    let new_brick = WallSection::new(curr_section.len().saturating_mul(2));
                    let old_brick =
                        std::mem::replace(unsafe { &mut *self.curr_section.get() }, new_brick);

                    self.past_sections.add_brick(old_brick);
                    continue;
                }
            }
        }
    }

    fn alloc_raw_value<T>(&self, value: T) -> NonNull<T> {
        let layout = Layout::new::<T>();
        let ptr: NonNull<T> = self.alloc_raw(layout).cast();
        unsafe {
            *(ptr.as_ptr()) = value;
        }
        ptr
    }
}

impl Clone for Wall<'_> {
    fn clone(&self) -> Self {
        Self::new(self.past_sections)
    }
}

#[derive(Debug, Default)]
struct PastSections {
    past_bricks: Mutex<Vec<WallSection>>,
}

impl PastSections {
    fn new() -> Self {
        Self::default()
    }

    fn add_brick(&self, brick: WallSection) {
        self.past_bricks.lock().push(brick);
    }
}

#[derive(Debug, Default)]
struct Castle {
    past_sections: PastSections,
}

impl Castle {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn wall(&self) -> Wall {
        Wall::new(&self.past_sections)
    }
}

pub struct Brick<'c, T> {
    data: NonNull<T>,
    castle_lifetime: PhantomData<&'c ()>,
}

impl<'c, T> Brick<'c, T> {
    pub fn new(x: T, wall: &Wall<'c>) -> Self {
        Self {
            data: wall.alloc_raw_value(x),
            castle_lifetime: PhantomData::default(),
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
        unsafe { self.data.as_ref() }
    }
}

impl<T: fmt::Debug> fmt::Debug for Brick<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

unsafe impl<T: Sync> Sync for Brick<'_, T> {}
unsafe impl<T: Send> Send for Brick<'_, T> {}

pub struct Row<'c, T> {
    data: NonNull<T>,
    length: usize,
    capacity: usize,
    castle_lifetime: PhantomData<&'c ()>,
}

const ROW_INITIAL_REALLOC_SIZE: usize = 4;
const ROW_REALLOC_MULTIPLIER: usize = 2;

impl<'c, T> Row<'c, T> {
    pub fn new(wall: &Wall<'c>) -> Self {
        Self::with_capacity(0, wall)
    }

    pub fn with_capacity(initial_capacity: usize, wall: &Wall<'c>) -> Self {
        let layout = Layout::array::<T>(initial_capacity).unwrap();
        let data = wall.alloc_raw(layout);
        Self {
            data: data.cast(),
            length: 0,
            capacity: initial_capacity,
            castle_lifetime: PhantomData::default(),
        }
    }

    pub fn reserve(&mut self, new_capacity: usize, wall: &Wall<'c>) {
        if new_capacity < self.capacity {
            // no-op
            return;
        }

        if new_capacity < self.length {
            panic!("Tried to reallocate with a capacity smaller than length");
        }

        let layout = Layout::array::<T>(new_capacity).unwrap();
        let new_data: NonNull<T> = wall.alloc_raw(layout).cast();

        // Safety: Both ranges are valid because they originate from wall.alloc_raw.
        unsafe {
            std::ptr::copy_nonoverlapping(self.data.as_ptr(), new_data.as_ptr(), self.length);
        }

        self.data = new_data;
        self.capacity = new_capacity;
    }

    pub fn push(&mut self, element: T, wall: &Wall<'c>) {
        if self.capacity < self.length + 1 {
            if self.capacity == 0 {
                self.reserve(ROW_INITIAL_REALLOC_SIZE, wall);
            } else {
                let new_capacity = self.capacity * ROW_REALLOC_MULTIPLIER;
                if new_capacity > isize::MAX as usize {
                    panic!("Reallocation target capacity is too large");
                }

                self.reserve(new_capacity, wall);
            }
        }

        unsafe { *self.data.as_ptr().offset(self.length as isize) = element };
        self.length += 1;
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

    pub fn capacity(&self) -> usize {
        self.capacity
    }
}

impl<T: fmt::Debug> fmt::Debug for Row<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Row ")?;
        self.deref().fmt(f)
    }
}

impl<T> Deref for Row<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        unsafe { std::slice::from_raw_parts(self.data.as_ptr() as *const T, self.length) }
    }
}

impl<T> DerefMut for Row<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { std::slice::from_raw_parts_mut(self.data.as_ptr(), self.length) }
    }
}

unsafe impl<T: Send> Send for Row<'_, T> {}

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
}

impl Deref for BrickString<'_> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        unsafe { std::str::from_utf8_unchecked(self.inner.deref()) }
    }
}

impl fmt::Debug for BrickString<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

#[cfg(test)]
mod test {
    use core::fmt;
    use std::{
        hint::black_box,
        sync::atomic::{AtomicI64, Ordering},
        time::{Duration, Instant},
    };

    use super::*;

    #[derive(Debug)]
    struct MyComplexStructBoxed {
        a: Box<i32>,
        b: Box<Box<[Box<i32>; 5]>>,
    }

    #[derive(Debug)]
    struct MyComplexStructWref<'w> {
        a: Brick<'w, i32>,
        b: Brick<'w, Brick<'w, [Brick<'w, i32>; 5]>>,
    }

    impl MyComplexStructBoxed {
        pub fn new() -> Self {
            Self {
                a: Box::new(3),
                b: Box::new(Box::new([
                    Box::new(4),
                    Box::new(5),
                    Box::new(6),
                    Box::new(7),
                    Box::new(8),
                ])),
            }
        }
    }

    impl<'w> MyComplexStructWref<'w> {
        pub fn new(wall: &Wall<'w>) -> Self {
            Self {
                a: Brick::new(3, wall),
                b: Brick::new(
                    Brick::new(
                        [
                            Brick::new(4, wall),
                            Brick::new(5, wall),
                            Brick::new(6, wall),
                            Brick::new(7, wall),
                            Brick::new(8, wall),
                        ],
                        wall,
                    ),
                    wall,
                ),
            }
        }
    }

    fn run_alloc_test<P, R: Send + Sync + fmt::Debug>(
        total_count: i32,
        total_threads: usize,
        pre_op: impl Fn() -> P + Send + Sync,
        op: impl Fn(&mut P, i32) -> R + Send + Sync,
    ) -> Duration {
        let pool = rayon::ThreadPoolBuilder::new().build().unwrap();
        let wall_elapsed = AtomicI64::new(0);

        pool.scope(|scope| {
            for _ in 0..total_threads {
                scope.spawn(|_| {
                    let mut p = pre_op();
                    for i in 0..total_count {
                        let start = Instant::now();
                        let result = op(&mut p, i);
                        let elapsed = start.elapsed().as_nanos() as i64;
                        black_box(result);
                        wall_elapsed.fetch_add(elapsed, Ordering::SeqCst);
                    }
                });
            }
        });

        Duration::from_nanos(wall_elapsed.load(Ordering::SeqCst) as u64)
    }

    #[test]
    fn alloc_test() {
        let total_count = 2000;
        let total_threads = 20;

        println!(
            "Generating {} objects inside {} thread(s)",
            total_count, total_threads
        );

        let castle = Castle::new();
        let elapsed = run_alloc_test(
            total_count,
            total_threads,
            || castle.wall(),
            |wall, _| MyComplexStructWref::new(wall),
        );
        println!(
            "Wall took {:?} in total, {:?} average",
            elapsed,
            elapsed / total_count as u32
        );

        let elapsed = run_alloc_test(
            total_count,
            total_threads,
            || {},
            |_, _| MyComplexStructBoxed::new(),
        );
        println!(
            "Box took {:?} in total, {:?} average",
            elapsed,
            elapsed / total_count as u32
        );

        let elapsed = run_alloc_test(total_count, total_threads, || {}, |_, _| {});
        println!(
            "Control took {:?} in total, {:?} average",
            elapsed,
            elapsed / total_count as u32
        );
    }

    #[test]
    fn row_test() {
        let castle = Castle::new();
        let wall = castle.wall();
        let mut row = Row::<i64>::new(&wall);
        row.reserve(10000000, &wall);

        for i in 0..10000000 {
            row.push(i, &wall);
        }

        println!("{:?}", row);
    }
}
