//! Arena allocator implementation for use within the Hash compiler sources.
//!
//! All rights reserved 2021 (c) The Hash Language authors

#![allow(dead_code)] // @@REMOVE
#![feature(llvm_asm)]

use atomicbox::AtomicBox;
use parking_lot::{Mutex, RwLock, RwLockUpgradableReadGuard};
use std::{
    alloc::{alloc, dealloc, handle_alloc_error, Layout},
    cell::{Cell, UnsafeCell},
    collections::HashMap,
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::{
        atomic::{self, AtomicBool, AtomicI64, AtomicPtr, AtomicUsize, Ordering},
        Arc,
    },
    time::{Duration, Instant},
};

/// @@TODO: maybe make the ARENA_PAGE_SIZE configurable via 'cfg'?
/// 1MiB
const BRICK_SIZE: usize = 1 << 20;

#[derive(Debug)]
struct Brick {
    data: NonNull<u8>,
    offset: AtomicUsize,
}

impl Brick {
    fn new() -> Self {
        let layout = Self::layout();
        let data = {
            let block = unsafe { alloc(layout) };
            NonNull::new(block).unwrap_or_else(|| handle_alloc_error(layout))
        };
        let offset = AtomicUsize::new(0);

        Self { data, offset }
    }

    fn layout() -> Layout {
        Layout::array::<u8>(BRICK_SIZE).unwrap()
    }

    fn alloc(&self, layout: Layout) -> Option<NonNull<u8>> {
        // Old value is start
        let start = {
            let layout_size = layout.size();

            // Here we perform a compare-exchange loop on the offset, to update it.
            let mut curr_offset = self.offset.load(Ordering::Acquire);
            loop {
                let new_offset = curr_offset + layout_size;
                if new_offset >= BRICK_SIZE {
                    // We cannot allocate.
                    return None;
                }

                match self.offset.compare_exchange_weak(
                    curr_offset,
                    new_offset,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => {
                        break curr_offset;
                    }
                    Err(next_curr_offset) => {
                        curr_offset = next_curr_offset;
                        continue;
                    }
                }
            }
        };

        // Pointer to return is `start` offset from self.data.
        let ptr = unsafe { NonNull::new_unchecked(self.data.as_ptr().offset(start as isize)) };
        Some(ptr)
    }

    fn remaining_capacity(&self) -> usize {
        BRICK_SIZE - self.offset.load(Ordering::Acquire)
    }
}

impl Drop for Brick {
    fn drop(&mut self) {
        let layout = Self::layout();
        unsafe {
            dealloc(self.data.as_ptr(), layout);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Wref<'w, T: ?Sized>(&'w T);

#[derive(Debug, PartialEq, Eq)]
pub struct Wmut<'w, T: ?Sized>(&'w mut T);

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

struct Wall {
    curr_brick: AtomicPtr<Brick>,
    allocating: AtomicBool,
    past_bricks: Mutex<Vec<Box<Brick>>>,
}

impl<'w> Wall
where
    Self: 'w,
{
    /// Create an arena
    pub fn new() -> Self {
        Self {
            curr_brick: AtomicPtr::new(Box::leak(Box::new(Brick::new()))),
            allocating: AtomicBool::new(false),
            past_bricks: Mutex::new(vec![]),
        }
    }

    fn alloc_raw(&self, layout: Layout) -> NonNull<u8> {
        loop {
            // Safety: pointer is owned, thus always valid.
            let brick = unsafe { &*self.curr_brick.load(Ordering::Relaxed) };

            // Should never be empty.
            match brick.alloc(layout) {
                Some(result) => {
                    break result;
                }
                None => {
                    // If no one is allocating, set to allocating.
                    match self.allocating.compare_exchange_weak(
                        false,
                        true,
                        Ordering::SeqCst,
                        Ordering::SeqCst,
                    ) {
                        Ok(_) => {
                            let new_brick = Box::leak(Box::new(Brick::new()));
                            let old_brick = self.curr_brick.swap(new_brick, Ordering::SeqCst);
                            self.allocating.store(false, Ordering::SeqCst);

                            // Put in past bricks
                            self.past_bricks
                                .lock()
                                // Safety: pointer was originally created from Box.
                                .push(unsafe { Box::from_raw(old_brick) });
                        }
                        // Someone is already allocating, fallback to continue
                        Err(_) => {}
                    };

                    continue;
                }
            }
        }
    }

    /// Allocate some type onto the wall, returning a mutable reference to the item.
    #[inline]
    pub fn make<T>(&self, object: T) -> Wmut<'w, T> {
        self.make_with(|| object)
    }

    /// Allocate some type onto the wall, returning a mutable reference to the item.
    #[inline]
    pub fn make_with<T>(&self, f: impl FnOnce() -> T) -> Wmut<'w, T> {
        let layout = Layout::new::<T>();
        let mut ptr: NonNull<T> = self.alloc_raw(layout).cast();
        unsafe {
            *(ptr.as_ptr()) = f();
        }
        Wmut(unsafe { ptr.as_mut() })
    }
}

unsafe impl Send for Wall {}
unsafe impl Sync for Wall {}

pub fn black_box<T>(mut dummy: T) -> T {
    unsafe {
        // FIXME: Cannot use `asm!` because it doesn't support MIPS and other architectures.
        llvm_asm!("" : : "r"(&mut dummy) : "memory" : "volatile");
    }

    dummy
}

fn run_alloc_test<R: Send + Sync + 'static>(
    total_count: i32,
    total_threads: usize,
    op: impl Fn(i32) -> R + Send + Sync + 'static,
) -> Duration {
    let mut wall_handles = Vec::with_capacity(total_threads);
    let op = Arc::new(op);

    let wall_elapsed = Arc::new(AtomicI64::new(0));
    for _ in 0..total_threads {
        let wall_elapsed = wall_elapsed.clone();
        let op = op.clone();
        wall_handles.push(std::thread::spawn(move || {
            for i in 0..total_count {
                let start = Instant::now();
                let result = op(i);
                let elapsed = start.elapsed().as_nanos() as i64;
                black_box(result);
                wall_elapsed.fetch_add(elapsed, Ordering::SeqCst);
            }
        }));
    }
    for handle in wall_handles {
        handle.join().unwrap();
    }

    Duration::from_nanos(wall_elapsed.load(Ordering::SeqCst) as u64)
}

#[cfg(test)]
mod test {
    use std::{
        sync::{
            atomic::{AtomicI64, AtomicIsize},
            Arc,
        },
        time::{Duration, Instant},
    };

    use super::*;

    #[test]
    fn alloc_test() {
        let total_count = 20000;
        let total_threads = 1;

        println!(
            "Generating {} numbers inside {} thread(s)",
            total_count, total_threads
        );

        let wall = &*Box::leak(Box::new(Wall::new()));
        let elapsed = run_alloc_test(total_count, total_threads, move |i| wall.make(i));
        println!(
            "Wall took {:?} in total, {:?} average",
            elapsed,
            elapsed / total_count as u32
        );

        let elapsed = run_alloc_test(total_count, total_threads, |i| Box::new(i));
        println!(
            "Box took {:?} in total, {:?} average",
            elapsed,
            elapsed / total_count as u32
        );

        let elapsed = run_alloc_test(total_count, total_threads, |_| {});
        println!(
            "Control took {:?} in total, {:?} average",
            elapsed,
            elapsed / total_count as u32
        );

        // let wall_ret1 = wall_objects1.into_iter().map(|i| *i).collect::<Vec<i32>>();
        // let wall_ret2 = wall_objects2.into_iter().map(|i| *i).collect::<Vec<i32>>();
        //

        // let rem = wall.brick.remaining_capacity();
        // println!(
        //     "remaining: {} out of {} bytes ({}% full)",
        //     rem,
        //     BRICK_SIZE,
        //     f64::from((BRICK_SIZE - rem) as u32) / f64::from(BRICK_SIZE as u32)
        // );

        // assert_eq!(wall_ret1, (1..=total_count).collect::<Vec<i32>>());
        // assert_eq!(
        //     wall_ret2,
        //     (total_count + 1..=total_count + total_count).collect::<Vec<i32>>()
        // );
    }
}
