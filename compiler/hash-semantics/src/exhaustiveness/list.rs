//! Data structures used within the exhaustiveness implementation to represent
//! list patterns.
use std::{cmp::max, iter::once};

/// Represents the kind of [Array], whether it is
/// of a fixed length or of a variable length.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ArrayKind {
    /// When the size of the array pattern is known.
    Fixed(usize),

    /// When the array pattern features a spread pattern, the
    /// first number is the length of the prefix elements, and
    /// the succeeding number is the length of the suffix
    /// elements.
    Var(usize, usize),
}

impl ArrayKind {
    /// Get the arity of the list, based on the kind. For
    /// [ArrayKind::Var], the `...` is treated as a single wild
    /// card and ignored for this purpose.
    fn arity(self) -> usize {
        match self {
            ArrayKind::Fixed(length) => length,
            ArrayKind::Var(prefix, suffix) => prefix + suffix,
        }
    }

    /// Whether this pattern includes patterns of length `other_len`.
    fn covers_length(self, other_len: usize) -> bool {
        match self {
            ArrayKind::Fixed(len) => len == other_len,
            ArrayKind::Var(prefix, suffix) => prefix + suffix <= other_len,
        }
    }
}

/// Representation of array patterns within the exhaustiveness sub-system.
/// [Array]s have an inner `kind` which denote whether this [Array] has a fixed
/// length or a variable length (which occurs when a `...` pattern) is present.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Array {
    /// The kind of pattern it is: fixed-length `[x, y]` or
    /// variable length `[x, ..., y]`.
    pub kind: ArrayKind,
}

impl Array {
    /// Construct a new [Array] with a provided kind.
    pub(crate) fn new(kind: ArrayKind) -> Self {
        Self { kind }
    }

    /// Compute the arity of the [Array].
    pub(crate) fn arity(self) -> usize {
        self.kind.arity()
    }

    /// Whether another [Array] would cover this [Array].
    pub(crate) fn is_covered_by(self, other: Self) -> bool {
        other.kind.covers_length(self.arity())
    }
}

#[derive(Debug)]
pub struct SplitVarList {
    /// The arity of the input slice.
    arity: usize,
    /// The smallest list bigger than any list seen. `max_list.arity()` is
    /// the length `L` described above.
    max_list: ArrayKind,
}

impl SplitVarList {
    pub fn new(prefix: usize, suffix: usize) -> Self {
        SplitVarList { arity: prefix + suffix, max_list: ArrayKind::Var(prefix, suffix) }
    }

    /// Pass a set of arrays relative to which to split this one.
    ///
    /// We don't need to split the [Array] if the kind is [ArrayKind::Fixed].
    pub fn split(&mut self, slices: impl Iterator<Item = ArrayKind>) {
        let ArrayKind::Var(max_prefix_len, max_suffix_len) = &mut self.max_list else {
            return;
        };

        // We grow `self.max_list` to be larger than all slices encountered, as
        // described above. For diagnostics, we keep the prefix and suffix
        // lengths separate, but grow them so that `L = max_prefix_len +
        // max_suffix_len`.
        let mut max_fixed_len = 0;

        for slice in slices {
            match slice {
                ArrayKind::Fixed(len) => {
                    max_fixed_len = max(max_fixed_len, len);
                }
                ArrayKind::Var(prefix, suffix) => {
                    *max_prefix_len = max(*max_prefix_len, prefix);
                    *max_suffix_len = max(*max_suffix_len, suffix);
                }
            }
        }

        // We want `L = max(L, max_fixed_len + 1)`, modulo the fact that we keep prefix
        // and suffix separate.
        //
        // This ensures that the size adjustment of `max_prefix_len` can't overflow
        if max_fixed_len + 1 >= *max_prefix_len + *max_suffix_len {
            *max_prefix_len = max_fixed_len + 1 - *max_suffix_len;
        }
    }

    /// Iterate over the partition of this slice.
    pub fn iter(&self) -> impl Iterator<Item = Array> + '_ {
        // We cover all arities in the range `(self.arity..infinity)`. We split that
        // range into two: lengths smaller than `max_slice.arity()` are treated
        // independently as fixed-lengths slices, and lengths above are captured
        // by `max_slice`.
        let smaller_lengths = self.arity..self.max_list.arity();

        smaller_lengths.map(ArrayKind::Fixed).chain(once(self.max_list)).map(Array::new)
    }
}
