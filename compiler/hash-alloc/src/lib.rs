//! Arena allocator implementation for use within the Hash compiler sources.
//!
//! All rights reserved 2021 (c) The Hash Language authors

#![allow(dead_code)] // @@REMOVE
#![feature(bench_black_box)]

use parking_lot::Mutex;
use std::{alloc::Layout, cell::{Cell, RefCell, UnsafeCell}, ops::{Deref, DerefMut}, ptr::NonNull};

/// @@TODO: maybe make the ARENA_PAGE_SIZE configurable via 'cfg'?
/// 1MiB
const BRICK_SIZE: usize = 1 << 20;

#[derive(Debug)]
struct Brick {
    data: [u8; BRICK_SIZE],
    offset: Cell<usize>,
}

impl Brick {
    fn new() -> Self {
        Self {
            data: [0; BRICK_SIZE],
            offset: Cell::new(0),
        }
    }

    fn alloc(&self, layout: Layout) -> Option<NonNull<u8>> {
        // Old value is start
        let start = {
            let layout_size = layout.size();

            let old_offset = self.offset.get();
            let new_offset = old_offset + layout_size;
            if new_offset >= BRICK_SIZE {
                if layout_size > BRICK_SIZE {
                    // This means we cannot even allocate this layout at all.
                    panic!("Tried to allocate an object on the castle that is too large!");
                }

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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Wref<'w, T: ?Sized>(&'w T);

#[derive(Debug, PartialEq, Eq)]
pub struct Wmut<'w, T: ?Sized>(&'w mut T);

impl<'w, T> Wmut<'w, T> {
    pub fn as_wref(self) -> Wref<'w, T> {
        Wref(self.0)
    }
}

impl<T> Deref for Wmut<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<T> DerefMut for Wmut<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

impl<T> Deref for Wref<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

pub type Wstr<'w> = Wref<'w, str>;
pub type Wslice<'w, T> = Wref<'w, [T]>;

struct Wall<'c> {
    curr_brick: RefCell<Box<Brick>>,
    past_bricks: &'c PastCastleBricks,
}

impl<'c> Wall<'c> {
    fn alloc_raw(&self, layout: Layout) -> NonNull<u8> {
        loop {
            match self.curr_brick.borrow().alloc(layout) {
                Some(result) => {
                    break result;
                }
                None => {
                    let new_brick = Box::new(Brick::new());
                    let old_brick = self.curr_brick.replace(new_brick);
                    self.past_bricks.add_brick(old_brick);
                    continue;
                }
            }
        }
    }

    /// Allocate some type onto the wall, returning a mutable reference to the item.
    #[inline]
    pub fn make<T>(&self, object: T) -> Wmut<'c, T> {
        self.make_with(|| object)
    }

    /// Allocate some type onto the wall, returning a mutable reference to the item.
    #[inline]
    pub fn make_with<T>(&self, f: impl FnOnce() -> T) -> Wmut<'c, T> {
        let layout = Layout::new::<T>();
        let mut ptr: NonNull<T> = self.alloc_raw(layout).cast();
        unsafe {
            *(ptr.as_ptr()) = f();
        }
        Wmut(unsafe { ptr.as_mut() })
    }
}

#[derive(Debug, Default)]
struct PastCastleBricks {
    past_bricks: Mutex<Vec<Box<Brick>>>,
}

impl PastCastleBricks {
    fn new() -> Self {
        Self::default()
    }

    fn add_brick(&self, brick: Box<Brick>) {
        self.past_bricks.lock().push(brick);
    }
}

#[derive(Debug, Default)]
struct Castle {
    past_bricks: PastCastleBricks,
}

impl Castle {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn wall(&self) -> Wall {
        Wall {
            curr_brick: RefCell::new(Box::new(Brick::new())),
            past_bricks: &self.past_bricks,
        }
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
        a: Wref<'w, i32>,
        b: Wref<'w, Wref<'w, [Wref<'w, i32>; 5]>>,
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
                a: wall.make(3).as_wref(),
                b: wall
                    .make(
                        wall.make([
                            wall.make(4).as_wref(),
                            wall.make(5).as_wref(),
                            wall.make(6).as_wref(),
                            wall.make(7).as_wref(),
                            wall.make(8).as_wref(),
                        ])
                        .as_wref(),
                    )
                    .as_wref(),
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
        let total_count = 200;
        let total_threads = 2;

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
}
