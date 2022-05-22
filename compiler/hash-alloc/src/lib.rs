//! Arena allocator implementation for use within the Hash compiler sources.
//!
//! All rights reserved 2022 (c) The Hash Language authors

pub mod brick;
pub mod collections;

use std::mem::{ManuallyDrop, MaybeUninit};

/// The root primitive of arena allocation.
///
/// A `Castle` can create [`Wall`]s, which in turn can allocate values onto an arena. The existence
/// of these two primitives, rather than a single one, is due to the requirement of thread-safety
/// in memory allocation. Each [`Wall`] in a `Castle` lives inside its own thread, and it cannot
/// cross thread boundaries (although the allocations themselves can).
///
/// This means that there is no need to acquire any mutex or lock whenever an allocation occurs,
/// but this is needed when a new [`Wall`] is created.
#[derive(Default)]
pub struct Castle {
    herd: bumpalo_herd::Herd,
}

impl std::fmt::Debug for Castle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Castle").finish()
    }
}

impl Castle {
    /// Create a new [`Castle`]. All values allocated within [`Wall`]s created from this castle
    /// will be dropped once the `Castle` is dropped.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new [`Wall`] inside this `Castle`. The created [`Wall`] lives as long as the
    /// reference to this `Castle`.
    pub fn wall(&self) -> Wall {
        Wall::with_member(self.herd.get(), self)
    }
}

/// A thread-unsafe object which can allocate memory inside a memory arena.
///
/// Some features of this style of allocation:
///
/// * Cost of allocation is really tiny (just an integer comparison and a pointer incrementation).
///
/// * All allocations are very well spatially localised---they are arranged sequentially in
/// memory. This means that traversing graph/tree structures allocated on the [`Wall`] is very
/// cache-friendly, as the elements will be right next to each other.
///
/// * All allocations live for the same amount of time, which is the lifetime of the underlying
/// [`Castle`]. However, values allocated inside a [`Wall`] can be dropped because the allocations
/// are wrapped in [`ManuallyDrop`]. For a more ergonomic way of allocating values and collections,
/// take a look at the [`collections`] and [`brick`] modules.
///
///
///  Currently, this is implemented using [`bumpalo`], but this will (probably) change in the
///  future as the compiler acquires more niche requirements.
pub struct Wall<'c> {
    castle: &'c Castle,
    member: bumpalo_herd::Member<'c>,
}

impl std::fmt::Debug for Wall<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Wall")
            .field("castle", &self.castle)
            .finish()
    }
}

impl<'c> Wall<'c> {
    /// Create a new [`Wall`] inside the given [`Castle`].
    ///
    /// Synonym for `castle.wall()`.
    pub fn new(castle: &'c Castle) -> Self {
        castle.wall()
    }

    /// *Bumpalo-specific*: create a wall with the given [`bumpalo_herd::Member`], which is the
    /// underlying `bumpalo` primitive that [`Wall`] uses.
    fn with_member(member: bumpalo_herd::Member<'c>, castle: &'c Castle) -> Self {
        Self { member, castle }
    }

    /// Get a reference to the [`Castle`] which this wall is part of.
    pub fn owning_castle(&self) -> &'c Castle {
        self.castle
    }

    /// Allocate a given value on the [`Wall`].
    ///
    /// This returns a mutable reference to the given value, wrapped in [`ManuallyDrop`] which
    /// allows one to drop the value even though it is still physically present in the arena. Keep
    /// in mind that this sort of manually dropping is an unsafe operation.
    pub fn alloc_value<T>(&self, value: T) -> &'c mut ManuallyDrop<T> {
        self.member.alloc(ManuallyDrop::new(value))
    }

    /// Allocate an uninitialised slice on the [`Wall`] with the given length.
    ///
    /// This returns a mutable reference to the allocated slice, wrapped in [`MaybeUninit`] and
    /// [`ManuallyDrop`]. All the values are initially set to `MaybeUninit::uninit()`.
    ///
    /// Despite the fact that `MaybeUninit` implies `ManuallyDrop`, Rust does not yet provide a stable
    /// way of in-place dropping a `MaybeUninit` (until [#63567](https://github.com/rust-lang/rust/issues/63567) lands).
    pub fn alloc_uninit_slice<T>(&self, len: usize) -> &'c mut [MaybeUninit<ManuallyDrop<T>>] {
        self.member
            .alloc_slice_fill_with(len, |_| MaybeUninit::uninit())
    }
}

// We will probably need more tests here once we replace bumpalo with a custom implementation
// again.
#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn alloc_simple_test() {
        const SIMPLE_VALUE: i32 = 42;

        let castle = Castle::new();
        let wall = castle.wall();

        let value = wall.alloc_value(SIMPLE_VALUE);

        let mut value_eq = ManuallyDrop::new(SIMPLE_VALUE);
        assert_eq!(value, &mut value_eq);
    }

    #[test]
    fn alloc_complex_test() {
        #[derive(Debug, PartialEq, Eq)]
        enum Color {
            Red,
            Blue,
            Green,
        }

        #[derive(Debug, PartialEq, Eq)]
        struct MyComplexStruct {
            a: i32,
            b: char,
            c: [Color; 3],
        }

        const COMPLEX_VALUE: MyComplexStruct = MyComplexStruct {
            a: 43,
            b: 'R',
            c: [Color::Red, Color::Green, Color::Blue],
        };

        let castle = Castle::new();
        let wall = castle.wall();

        let value = wall.alloc_value(COMPLEX_VALUE);
        let mut value_eq = ManuallyDrop::new(COMPLEX_VALUE);

        assert_eq!(value, &mut value_eq);
    }

    #[test]
    fn alloc_array_test() {
        const ARRAY_SIZE: usize = 100;

        let castle = Castle::new();
        let wall = castle.wall();

        let values = wall.alloc_uninit_slice(ARRAY_SIZE);

        // initialise all
        for (i, v) in values.iter_mut().enumerate() {
            *v = MaybeUninit::new(ManuallyDrop::new(i.pow(2)));
        }

        let mut values_eq = (0..ARRAY_SIZE)
            .map(|i| ManuallyDrop::new(i.pow(2)))
            .collect::<Vec<_>>();

        assert_eq!(
            unsafe {
                std::mem::transmute::<
                    &mut [MaybeUninit<ManuallyDrop<usize>>],
                    &mut [ManuallyDrop<usize>],
                >(values)
            },
            &mut values_eq
        );
    }
}
