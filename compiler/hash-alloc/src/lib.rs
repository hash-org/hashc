//! Arena allocator implementation for use within the Hash compiler sources.
//!
//! All rights reserved 2021 (c) The Hash Language authors

#![allow(dead_code)] // @@REMOVE

use std::cell::Cell;

/// @@TODO: maybe make the ARENA_PAGE_SIZE configurable via 'cfg'?
/// 1MiB
const ARENA_PAGE_SIZE: usize = 1024 * 1024;

pub struct Arena {
    pages: Cell<Vec<Vec<u8>>>,
    start: Cell<*mut u8>,
    offset: Cell<usize>,
}

/// `Sync` is unsafe but `Send` is totally fine!
unsafe impl Send for Arena {}

/// Implementation and API for allocation for within the Arena allocator.
impl Arena {
    /// Create a new arena with the default [ARENA_BLOCK] size as the initial capacity.
    pub fn new() -> Self {
        let mut pages = vec![Vec::with_capacity(ARENA_PAGE_SIZE)];
        let start = pages[0].as_mut_ptr();

        Arena {
            pages: Cell::new(pages),
            start: Cell::new(start),
            offset: Cell::new(0),
        }
    }

    /// Allocate some type onto the arena, returning a mutable reference to the item.
    #[inline]
    pub fn alloc<'arena, T>(&'arena self, _item: T) -> &'arena mut T {
        todo!()
    }

    /// Allocate a slice of some type onto the arena.
    pub fn alloc_slice<'arena, T>(&'arena self, _item: &[T]) -> &'arena [T] {
        todo!()
    }

    /// Allocate a vector of some type onto the arena. This will internally convert the vector into
    /// a slice and then allocate it using the [alloc_slice] method.
    pub fn alloc_vec<'arena, T>(&'arena self, mut _val: Vec<T>) -> &'arena [T] {
        todo!()
    }

    /// Allocate a primitive string onto the arena. Internally, this will be converted into
    /// bytes and just placed into the arena.
    pub fn alloc_str<'arena>(&'arena self, _val: &str) -> &'arena str {
        todo!()
    }

    /// Allocate a [String] onto the arena. Internally, this will be converted into
    /// bytes and just placed into the arena.
    pub fn alloc_string<'arena>(&'arena self, _val: String) -> &'arena str {
        todo!()
    }

    /// Allocate a specified amount of bytes onto the arena, effectively reserving them. The function
    /// returns a reference to the region that is to be allocated.
    fn alloc_bytes(&self, size: usize) -> *mut u8 {
        self.alloc_block(Vec::with_capacity(size))
    }

    /// Allocate another page onto the arena, the page is represented as a vector of bytes of unspecified
    /// size.
    #[inline]
    fn alloc_block(&self, mut page: Vec<u8>) -> *mut u8 {
        let ptr = page.as_mut_ptr();

        // take the old pages, push the new one
        let mut temp = self.pages.replace(Vec::new());
        temp.push(page);

        // essentially, re-allocate the old pages with the new ones
        self.pages.replace(temp);

        ptr
    }

    /// Grow the arena by a single page, specified by the [ARENA_BLOCK].
    fn grow(&self) {
        let start = self.alloc_block(Vec::with_capacity(ARENA_PAGE_SIZE));
        self.start.set(start);
    }

    /// Reset the current start position to the beginning of the current page, essentially
    /// evicting everything allocated on the current page and ready to be overwritten.
    #[inline]
    unsafe fn evict_page(&self) {
        self.offset.set(0)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn allocate_some_stuff() {
        let arena = Arena::new();

        assert_eq!(arena.alloc(0u64), &0);
        assert_eq!(arena.alloc(42u64), &42);
        assert_eq!(arena.alloc(0x8000000u64), &0x8000000u64);

        assert_eq!(arena.offset.get(), 8 * 3);

        // For inspecting internals
        let mut arena = arena;

        assert_eq!(arena.pages.get_mut().len(), 1);
    }
}
