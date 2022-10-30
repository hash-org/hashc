//! Some assertion utilities for use within the compiler source.

/// Ensure that the size of a particular data structure matches the expected
/// size.
pub macro static_assert_size($ty:ty, $size:expr) {
    const _: [(); $size] = [(); ::std::mem::size_of::<$ty>()];
}
