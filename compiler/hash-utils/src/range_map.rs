//! A range map encodes ranges as keys that map to
//! values. This is useful for looking up particular values
//! when the key can be a range of values.

extern crate num_traits;

use std::{cmp::Ordering, fmt, ops::RangeInclusive};

use itertools::Itertools;
use num_traits::PrimInt;

/// A wrapper around a [RangeInclusive] which is copyable, and hence is
/// used by the [RangeMap] in order to store the ranges.
#[derive(Copy, Clone, Hash, Debug, PartialEq, PartialOrd, Eq, Ord)]
pub struct Range<Idx> {
    start: Idx,
    end: Idx,
}

impl<T: fmt::Display> fmt::Display for Range<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..={}", self.start, self.end)
    }
}

impl<Idx: PrimInt> Range<Idx> {
    pub fn contains(&self, item: Idx) -> bool {
        self.start <= item && item <= self.end
    }
}

impl<T: PrimInt> PartialEq<T> for Range<T> {
    fn eq(&self, x: &T) -> bool {
        self.contains(*x)
    }
}

impl<T: PrimInt> PartialOrd<T> for Range<T> {
    fn partial_cmp(&self, x: &T) -> Option<Ordering> {
        if self.end < *x {
            Some(Ordering::Less)
        } else if self.start > *x {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

impl<I> From<RangeInclusive<I>> for Range<I> {
    fn from(value: RangeInclusive<I>) -> Self {
        let (start, end) = value.into_inner();
        Range { start, end }
    }
}

#[derive(Clone, Debug, Default)]
pub struct RangeMap<I, V> {
    /// The store that stores the [Range] which maps a range of keys
    /// to a value.
    store: Vec<(Range<I>, V)>,
}

impl<I: fmt::Display, V: fmt::Display> fmt::Display for RangeMap<I, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (key, value) in self.store.iter() {
            writeln!(f, "{key}: {value}")?;
        }

        Ok(())
    }
}

impl<I: PrimInt + Clone + Copy, V> RangeMap<I, V> {
    /// Create a new empty [RangeMap].
    pub fn new() -> Self {
        Self { store: vec![] }
    }

    /// Create a new [RangeMap] with a pre-allocated storage of a given
    /// size.
    pub fn with_capacity(length: usize) -> Self {
        Self { store: Vec::with_capacity(length) }
    }

    /// Create a new [RangeMap] with specified ranges that are assumed
    /// to be in order.
    pub fn populated(items: Vec<(RangeInclusive<I>, V)>) -> Self {
        let map = Self {
            store: items
                .into_iter()
                .map(|(r, v)| (r.into(), v))
                .sorted_by_key(|(range, _): &(Range<I>, _)| range.start)
                .collect_vec(),
        };

        assert!(map.verify(), "range map contains overlapping keys, which is not valid");
        map
    }

    /// Verify that the [RangeMap] does not contain any overlapping
    /// ranges.
    fn verify(&self) -> bool {
        for pair in self.store.windows(2) {
            let (left, right) = (pair[0].0, pair[1].0);

            if left.end >= right.start {
                return false;
            }
        }

        true
    }

    /// Insert a new key-value pair into the [RangeMap].
    pub fn insert(&mut self, key: RangeInclusive<I>, value: V) {
        let overlaps = |left: &Range<I>, right: &Range<I>| {
            if left.start >= right.start && left.end <= right.end {
                return true;
            }

            left.contains(right.start) || left.contains(right.end)
        };

        let key: Range<_> = key.into();

        for (index, (item, _)) in self.store.iter().enumerate() {
            if overlaps(item, &key) {
                panic!("keys are not allowed to overlap in a range map")
            }

            if key.start > item.end {
                continue;
            }

            // we've found the right spot to insert the key
            if key.end < item.start {
                self.store.insert(index, (key, value));
                return;
            }
        }

        // If we've reached the end, then we can just push the key
        // into the store.
        self.store.push((key, value))
    }

    /// Append a line range to the end of the [RangeMap] assuming that
    /// the final range does not overlap with any existing ranges.
    pub fn append(&mut self, key: RangeInclusive<I>, value: V) {
        let key: Range<_> = key.into();

        // If the store is empty, we can just immediately push the range
        // into the map, and exit early. Otherwise, we ensure that the
        // range does not overlap with the last range in the map.
        if let Some((last, _)) = self.store.last() {
            if last.end >= key.start {
                panic!("keys are not allowed to overlap in a range map")
            }
        }

        self.store.push((key, value));
    }

    /// Get the position of an element within the range map.
    pub fn index(&self, key: I) -> Option<usize> {
        self.store.binary_search_by(|(r, _)| r.partial_cmp(&key).unwrap()).ok()
    }

    /// Get the value from the given key.
    pub fn find(&self, key: I) -> Option<&V> {
        let pos = self.index(key)?;

        self.store.get(pos).map(|(_, value)| value)
    }

    /// Iterate over the key and value pairs currently in the
    /// [RangeMap].
    pub fn iter(&self) -> impl Iterator<Item = (&Range<I>, &V)> {
        self.store.iter().map(|(r, v)| (r, v))
    }
}

#[cfg(test)]
mod test_super {
    use super::*;

    #[test]
    fn test_range_map() {
        let map = RangeMap::populated(vec![(0..=10, 'a'), (11..=20, 'b'), (21..=30, 'c')]);

        // A
        assert_eq!(map.find(2), Some(&'a'));
        assert_eq!(map.find(7), Some(&'a'));
        assert_eq!(map.find(0), Some(&'a'));

        // B
        assert_eq!(map.find(11), Some(&'b'));
        assert_eq!(map.find(15), Some(&'b'));
        assert_eq!(map.find(20), Some(&'b'));

        // C
        assert_eq!(map.find(21), Some(&'c'));
        assert_eq!(map.find(25), Some(&'c'));
        assert_eq!(map.find(30), Some(&'c'));

        // Nothing
        assert_eq!(map.find(31), None);
        assert_eq!(map.find(1239), None);
    }

    #[test]
    fn test_range_map_insert() {
        let mut map = RangeMap::populated(vec![(0..=10, 'a'), (15..=20, 'c'), (21..=30, 'd')]);

        // Insert a 11-14 range with 'b'
        map.insert(11..=14, 'd');
        assert_eq!(map.find(12), Some(&'d'));
        println!("{}", map);

        // Insert into empty map
        let mut map = RangeMap::new();
        map.insert(0..=10, 'a');
        println!("{}", map);
    }

    #[test]
    #[should_panic]
    fn test_invalid_range_map_insert() {
        let mut map = RangeMap::populated(vec![(0..=10, 'a'), (15..=20, 'c'), (21..=30, 'd')]);

        // Insert a 10-14 range with 'b'
        //
        // @@Note: this should panic since the map disallows overlapping ranges.
        map.insert(10..=14, 'd');
        println!("{}", map);
    }

    #[test]
    #[should_panic]
    fn test_invalid_range_map() {
        // @@Note: this should panic since the provided ranges overlap.
        let map = RangeMap::populated(vec![
            (0..=10, 'a'),
            (10..=14, 'd'),
            (15..=20, 'c'),
            (21..=30, 'd'),
        ]);
        println!("{}", map);
    }
}
