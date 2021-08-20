//! Arena allocator implementation for use within the Hash compiler sources.
//!
//! All rights reserved 2021 (c) The Hash Language authors

#![allow(dead_code)] // @@REMOVE
#![feature(bench_black_box)]

pub mod brick;
pub mod collections;

use std::mem::{ManuallyDrop, MaybeUninit};

pub struct Wall<'c> {
    member: bumpalo_herd::Member<'c>,
}

impl<'c> Wall<'c> {
    pub fn new(castle: &'c Castle) -> Self {
        castle.wall()
    }

    pub fn allocated_bytes(&self) -> usize {
        self.member.as_bump().chunk_capacity()
    }

    pub fn used_bytes(&self) -> usize {
        self.member.as_bump().allocated_bytes()
    }

    fn with_member(member: bumpalo_herd::Member<'c>) -> Self {
        Self { member }
    }

    fn alloc_value<T>(&self, value: T) -> &'c mut ManuallyDrop<T> {
        self.member.alloc(ManuallyDrop::new(value))
    }

    fn alloc_uninit_slice<T>(&self, len: usize) -> &'c mut [MaybeUninit<ManuallyDrop<T>>] {
        self.member
            .alloc_slice_fill_with(len, |_| MaybeUninit::uninit())
    }
}

#[derive(Default)]
pub struct Castle {
    herd: bumpalo_herd::Herd,
}

impl Castle {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn wall<'c>(&'c self) -> Wall<'c> {
        Wall::with_member(self.herd.get())
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

    use crate::{brick::Brick, collections::row::Row};

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

        let _row: Row<i32> = row![&wall];

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
    }
}
