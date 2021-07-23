//! Arena allocator implementation for use within the Hash compiler sources.
//!
//! All rights reserved 2021 (c) The Hash Language authors

#![allow(dead_code)] // @@REMOVE
#![feature(bench_black_box)]
#![feature(maybe_uninit_extra)]

use core::fmt;
use parking_lot::Mutex;
use std::{
    alloc::Layout,
    cell::{Cell, UnsafeCell},
    mem::{ManuallyDrop, MaybeUninit},
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

/// @@TODO: maybe make the ARENA_PAGE_SIZE configurable via 'cfg'?
/// 1MiB
const INITIAL_SECTION_SIZE: usize = 1 << 20;

const RECLAIM_SECTION_MIN_REMAINING: usize = 1 << 8;

#[derive(Debug)]
struct WallSection {
    data: UnsafeCell<Box<[MaybeUninit<u8>]>>,
    offset: Cell<usize>,
}

impl WallSection {
    fn new() -> Self {
        WallSection::with_capacity(INITIAL_SECTION_SIZE)
    }

    fn with_capacity(capacity: usize) -> Self {
        Self {
            data: UnsafeCell::new(vec![MaybeUninit::uninit(); capacity].into_boxed_slice()),
            offset: Cell::new(0),
        }
    }

    fn alloc(&self, layout: Layout) -> Option<NonNull<MaybeUninit<u8>>> {
        // Old value is start
        let start = {
            let layout_size = layout.size();

            let old_offset = self.offset.get();
            let new_offset = old_offset + layout_size;

            // Safety: no one has access to data right now.
            let max_offset = unsafe { &*self.data.get() }.len();
            if new_offset >= max_offset {
                // We cannot allocate.
                return None;
            }
            self.offset.set(new_offset);

            old_offset
        };

        // Safety: no one has access to data right now, previous reference (max_offset) has been
        // dropped.
        let data_ptr = unsafe { &mut *self.data.get() }.as_mut_ptr();

        // Pointer to return is `start` offset from self.data.
        // Safety: we have ensured that the layout fits on the brick.
        //
        // Safety: ranges are never overlapping, so we don't need to care about aliasing. We can
        // safely return this pointer, given that the user only accesses data within
        //  0..layout.size()
        let ptr = unsafe {
            // @@TODO: what about integer overflow on start?
            NonNull::new_unchecked(data_ptr.offset(start as isize))
        };
        Some(ptr)
    }

    fn allocated_bytes(&self) -> usize {
        // Safety: no one has reference access to data length.
        unsafe { &*self.data.get() }.len()
    }

    fn used_bytes(&self) -> usize {
        self.offset.get()
    }

    fn remaining_bytes(&self) -> usize {
        self.allocated_bytes() - self.used_bytes()
    }
}

#[derive(Debug)]
pub struct Wall<'c> {
    curr_section: ManuallyDrop<UnsafeCell<WallSection>>,
    castle: &'c Castle,
}

impl<'c> Wall<'c> {
    pub fn new(castle: &'c Castle) -> Self {
        Self {
            curr_section: ManuallyDrop::new(UnsafeCell::new(WallSection::new())),
            castle,
        }
    }

    pub fn with_capacity(capacity: usize, castle: &'c Castle) -> Self {
        Self {
            curr_section: ManuallyDrop::new(UnsafeCell::new(WallSection::with_capacity(capacity))),
            castle,
        }
    }

    pub fn allocated_bytes(&self) -> usize {
        // Safety: no one else has a mutable reference to curr_section, and we are only reading
        unsafe { &*self.curr_section.get() }.allocated_bytes()
    }

    pub fn used_bytes(&self) -> usize {
        // Safety: no one else has a mutable reference to curr_section, and we are only reading
        unsafe { &*self.curr_section.get() }.used_bytes()
    }

    fn with_section(section: WallSection, castle: &'c Castle) -> Self {
        Self {
            curr_section: ManuallyDrop::new(UnsafeCell::new(section)),
            castle,
        }
    }

    fn alloc_raw(&self, layout: Layout) -> NonNull<MaybeUninit<u8>> {
        loop {
            let curr_section = unsafe { &*self.curr_section.get() };
            match curr_section.alloc(layout) {
                Some(result) => {
                    break result;
                }
                None => {
                    // New capacity is largest of: requested size, or current allocated bytes * 2.
                    // @@Improvement: potential for improvement in estimation?
                    let new_capacity = usize::max(
                        layout.size(),
                        curr_section.allocated_bytes().saturating_mul(2),
                    );

                    let new_wall_section = self
                        .castle
                        .new_or_reclaimed_section_with_capacity(new_capacity);

                    // Drop read access to curr_section.
                    drop(curr_section);

                    // Safety: no one has read access to self.curr_section right now.
                    let old_wall_section = std::mem::replace(
                        unsafe { &mut *self.curr_section.get() },
                        new_wall_section,
                    );

                    self.castle.reclaim_section(old_wall_section);
                    continue;
                }
            }
        }
    }

    fn alloc_value<T>(&self, value: T) -> &'c mut T {
        let layout = Layout::new::<T>();
        let mut ptr: NonNull<MaybeUninit<T>> = self.alloc_raw(layout).cast();
        unsafe {
            *(ptr.as_ptr()) = MaybeUninit::new(value);
        }
        unsafe { ptr.as_mut().assume_init_mut() }
    }

    fn alloc_uninit_slice<T>(&self, len: usize) -> &'c mut [MaybeUninit<T>] {
        let layout = Layout::array::<T>(len).unwrap();
        let ptr: NonNull<MaybeUninit<T>> = self.alloc_raw(layout).cast();
        unsafe { std::slice::from_raw_parts_mut(ptr.as_ptr(), len) }
    }
}

impl Drop for Wall<'_> {
    fn drop(&mut self) {
        // Reclaim the last section
        let section = unsafe { ManuallyDrop::take(&mut self.curr_section) }.into_inner();
        self.castle.reclaim_section(section);
    }
}

impl Clone for Wall<'_> {
    fn clone(&self) -> Self {
        self.castle.wall()
    }
}

#[derive(Debug, Default)]
struct PastSections {
    past_sections: Mutex<Vec<WallSection>>,
}

impl PastSections {
    fn new() -> Self {
        Self::default()
    }

    fn add_section(&self, brick: WallSection) {
        self.past_sections.lock().push(brick);
    }

    fn take_section(&self) -> Option<WallSection> {
        self.past_sections.lock().pop()
    }

    fn allocated_bytes(&self) -> usize {
        self.past_sections
            .lock()
            .iter()
            .map(|sec| sec.allocated_bytes())
            .sum()
    }

    fn used_bytes(&self) -> usize {
        self.past_sections
            .lock()
            .iter()
            .map(|sec| sec.used_bytes())
            .sum()
    }
}

#[derive(Debug, Default)]
pub struct Castle {
    full_sections: PastSections,
    reclaimable_sections: PastSections,
}

impl Castle {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn wall_with_capacity(&self, capacity: usize) -> Wall {
        Wall::with_section(self.new_or_reclaimed_section_with_capacity(capacity), self)
    }

    pub fn wall(&self) -> Wall {
        Wall::with_section(self.new_or_reclaimed_section(), self)
    }

    pub fn past_allocated_bytes(&self) -> usize {
        self.full_sections.allocated_bytes() + self.reclaimable_sections.allocated_bytes()
    }

    pub fn past_used_bytes(&self) -> usize {
        self.full_sections.used_bytes() + self.reclaimable_sections.used_bytes()
    }

    fn new_or_reclaimed_section_with_capacity(&self, capacity: usize) -> WallSection {
        match self.reclaimable_sections.take_section() {
            Some(section) if section.remaining_bytes() >= capacity => section,
            _ => WallSection::with_capacity(capacity),
        }
    }

    fn new_or_reclaimed_section(&self) -> WallSection {
        match self.reclaimable_sections.take_section() {
            Some(section) => section,
            None => WallSection::new(),
        }
    }

    fn reclaim_section(&self, section: WallSection) {
        if section.remaining_bytes() >= RECLAIM_SECTION_MIN_REMAINING {
            self.reclaimable_sections.add_section(section);
        } else {
            self.full_sections.add_section(section);
        }
    }
}

pub struct Brick<'c, T> {
    data: &'c mut T,
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

pub struct Row<'c, T> {
    data: &'c mut [MaybeUninit<T>],
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
        if new_capacity < self.capacity() {
            // no-op
            return;
        }

        if new_capacity < self.len() {
            panic!("Tried to reallocate with a capacity smaller than length");
        }

        println!("Reserving {}, current {}", new_capacity, self.capacity());
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
        *unsafe { self.data.get_unchecked_mut(self.len()) } = MaybeUninit::new(element);
        self.length += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len() == 0 {
            return None;
        }

        let last_element = std::mem::replace(
            unsafe { self.data.get_unchecked_mut(self.len() - 1) },
            MaybeUninit::uninit(),
        );
        self.length -= 1;

        Some(unsafe { last_element.assume_init() })
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
}

#[macro_export]
macro_rules! row {
    ($wall:expr) => { Row::new($wall) };
    ($wall:expr; $($item:expr),*) => { Row::from_iter([$($item,)*], $wall) };
    ($wall:expr; $($item:expr,)*) => { Row::from_iter([$($item,)*], $wall) };
    ($wall:expr; $item:expr; $count:expr) => { Row::from_iter(std::iter::repeat($item).take($count), $wall) };
}

impl<T: fmt::Debug> fmt::Debug for Row<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T> Deref for Row<'_, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // Safety: values until self.length are initialised.
        unsafe { std::mem::transmute::<&[MaybeUninit<T>], &[T]>(&self.data[0..self.length]) }
    }
}

impl<T> DerefMut for Row<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Safety: values until self.length are initialised.
        unsafe {
            std::mem::transmute::<&mut [MaybeUninit<T>], &mut [T]>(&mut self.data[0..self.length])
        }
    }
}

impl<T> Drop for Row<'_, T> {
    fn drop(&mut self) {
        // Drop elements until self.length
        for x in (&mut self.data[0..self.length]).into_iter() {
            unsafe {
                x.assume_init_drop();
            }
        }
    }
}

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
        b: Box<Vec<Box<i32>>>,
    }

    #[derive(Debug)]
    struct MyComplexStructWref<'w> {
        a: Brick<'w, i32>,
        b: Brick<'w, Row<'w, Brick<'w, i32>>>,
    }

    impl MyComplexStructBoxed {
        pub fn new() -> Self {
            Self {
                a: Box::new(3),
                b: Box::new(vec![
                    Box::new(4),
                    Box::new(5),
                    Box::new(6),
                    Box::new(7),
                    Box::new(8),
                ]),
            }
        }
    }

    impl<'w> MyComplexStructWref<'w> {
        pub fn new(wall: &Wall<'w>) -> Self {
            Self {
                a: Brick::new(3, wall),
                b: Brick::new(
                    row![wall;
                        Brick::new(4, wall),
                        Brick::new(5, wall),
                        Brick::new(6, wall),
                        Brick::new(7, wall),
                        Brick::new(8, wall),
                    ],
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

        println!(
            "used {}, total {}",
            wall.used_bytes(),
            wall.allocated_bytes()
        );

        let row: Row<i32> = row![&wall];

        println!(
            "used {}, total {}",
            wall.used_bytes(),
            wall.allocated_bytes()
        );
        let mut row2 = row![&wall; 1, 2, 3];

        println!(
            "used {}, total {}",
            wall.used_bytes(),
            wall.allocated_bytes()
        );
        let mut row3 = row![&wall; 10; 5000000];

        println!(
            "used {}, total {}",
            wall.used_bytes(),
            wall.allocated_bytes()
        );

        row3.push(4, &wall);
        let el = row2.pop();
        println!("{:?}", el);

        println!(
            "used {}, total {}",
            wall.used_bytes(),
            wall.allocated_bytes()
        );
        let el = row2.pop();
        println!("{:?}", el);

        println!(
            "used {}, total {}",
            wall.used_bytes(),
            wall.allocated_bytes()
        );
        let el = row2.pop();
        println!("{:?}", el);

        println!(
            "used {}, total {}",
            wall.used_bytes(),
            wall.allocated_bytes()
        );
        let el = row2.pop();
        println!("{:?}", el);

        println!(
            "used {}, total {}",
            wall.used_bytes(),
            wall.allocated_bytes()
        );
        let el = row2.pop();
        println!("{:?}", el);

        println!(
            "used {}, total {}",
            wall.used_bytes(),
            wall.allocated_bytes()
        );

        println!(
            "castle past used {}, total {}",
            castle.past_used_bytes(),
            castle.past_allocated_bytes()
        );
    }
}
