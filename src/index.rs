// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Indexing support for [`CopyStackVec`](crate::CopyStackVec).
//!
//! This module provides `Index` and `IndexMut` impls that mirror slice behavior:
//! - panics on out-of-bounds;
//! - supports all standard range forms, including inclusive ranges;
//! - views are restricted to the initialized prefix `[0..len)`.

// Crate imports
use crate::vec::CopyStackVec;

// Core imports
use core::ops::{
    Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};

impl<T: Copy, const N: usize> Index<usize> for CopyStackVec<T, N> {
    type Output = T;
    fn index(&self, i: usize) -> &Self::Output {
        &self.as_slice()[i]
    }
}

// Read-only ranges
impl<T: Copy, const N: usize> Index<Range<usize>> for CopyStackVec<T, N> {
    type Output = [T];
    fn index(&self, r: Range<usize>) -> &Self::Output {
        &self.as_slice()[r]
    }
}
impl<T: Copy, const N: usize> Index<RangeFrom<usize>> for CopyStackVec<T, N> {
    type Output = [T];
    fn index(&self, r: RangeFrom<usize>) -> &Self::Output {
        &self.as_slice()[r]
    }
}
impl<T: Copy, const N: usize> Index<RangeTo<usize>> for CopyStackVec<T, N> {
    type Output = [T];
    fn index(&self, r: RangeTo<usize>) -> &Self::Output {
        &self.as_slice()[r]
    }
}
impl<T: Copy, const N: usize> Index<RangeToInclusive<usize>> for CopyStackVec<T, N> {
    type Output = [T];
    fn index(&self, r: RangeToInclusive<usize>) -> &Self::Output {
        &self.as_slice()[r]
    }
}
impl<T: Copy, const N: usize> Index<RangeInclusive<usize>> for CopyStackVec<T, N> {
    type Output = [T];
    fn index(&self, r: RangeInclusive<usize>) -> &Self::Output {
        &self.as_slice()[r]
    }
}
impl<T: Copy, const N: usize> Index<RangeFull> for CopyStackVec<T, N> {
    type Output = [T];
    fn index(&self, _: RangeFull) -> &Self::Output {
        self.as_slice()
    }
}

// Mutable ranges
impl<T: Copy, const N: usize> IndexMut<usize> for CopyStackVec<T, N> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        &mut self.as_mut_slice()[i]
    }
}
impl<T: Copy, const N: usize> IndexMut<Range<usize>> for CopyStackVec<T, N> {
    fn index_mut(&mut self, r: Range<usize>) -> &mut Self::Output {
        &mut self.as_mut_slice()[r]
    }
}
impl<T: Copy, const N: usize> IndexMut<RangeFrom<usize>> for CopyStackVec<T, N> {
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut Self::Output {
        &mut self.as_mut_slice()[r]
    }
}
impl<T: Copy, const N: usize> IndexMut<RangeTo<usize>> for CopyStackVec<T, N> {
    fn index_mut(&mut self, r: RangeTo<usize>) -> &mut Self::Output {
        &mut self.as_mut_slice()[r]
    }
}
impl<T: Copy, const N: usize> IndexMut<RangeToInclusive<usize>> for CopyStackVec<T, N> {
    fn index_mut(&mut self, r: RangeToInclusive<usize>) -> &mut Self::Output {
        &mut self.as_mut_slice()[r]
    }
}
impl<T: Copy, const N: usize> IndexMut<RangeInclusive<usize>> for CopyStackVec<T, N> {
    fn index_mut(&mut self, r: RangeInclusive<usize>) -> &mut Self::Output {
        &mut self.as_mut_slice()[r]
    }
}
impl<T: Copy, const N: usize> IndexMut<RangeFull> for CopyStackVec<T, N> {
    fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
        self.as_mut_slice()
    }
}

#[cfg(test)]
mod tests {
    // Imports
    use super::CopyStackVec;

    #[test]
    fn test_ranges() {
        let mut v: CopyStackVec<i32, 6> = CopyStackVec::try_from(&[0, 1, 2, 3, 4][..]).unwrap();
        assert_eq!(&v[1..3], &[1, 2]);
        v[1..3].copy_from_slice(&[10, 20]);
        assert_eq!(v.as_slice(), &[0, 10, 20, 3, 4]);
    }

    #[test]
    #[should_panic]
    fn test_oob_panics() {
        let v: CopyStackVec<i32, 2> = CopyStackVec::default();
        let _ = v[0];
    }

    #[test]
    fn test_indexing_and_ranges_full_suite() {
        let mut v: CopyStackVec<i32, 6> = CopyStackVec::try_from(&[0, 1, 2, 3, 4][..]).unwrap();

        assert_eq!(v[0], 0);
        assert_eq!(&v[1..3], &[1, 2]);
        assert_eq!(&v[2..], &[2, 3, 4]);
        assert_eq!(&v[..3], &[0, 1, 2]);
        assert_eq!(&v[..=2], &[0, 1, 2]);
        assert_eq!(&v[1..=3], &[1, 2, 3]);
        assert_eq!(&v[..], &[0, 1, 2, 3, 4]);

        v[1..3].copy_from_slice(&[10, 20]);
        assert_eq!(v.as_slice(), &[0, 10, 20, 3, 4]);
    }

    #[test]
    fn test_empty_ranges_work() {
        let v: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        // Empty slices should be valid and equal to []
        assert_eq!(&v[1..1], &[] as &[i32]);
        assert_eq!(&v[..0], &[] as &[i32]);
        assert_eq!(&v[3..3], &[] as &[i32]);
    }

    #[test]
    #[should_panic]
    #[allow(clippy::reversed_empty_ranges)]
    fn test_inverted_range_panics() {
        let v: CopyStackVec<i32, 3> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        let _ = &v[2..1];
    }

    #[test]
    fn test_mut_inclusive_range() {
        let mut v: CopyStackVec<i32, 6> = CopyStackVec::try_from(&[0, 1, 2, 3][..]).unwrap();
        v[1..=2].copy_from_slice(&[9, 8]);
        assert_eq!(v.as_slice(), &[0, 9, 8, 3]);
    }

    #[test]
    #[should_panic]
    fn inclusive_upper_oob_panics() {
        let v: CopyStackVec<i32, 3> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        let _ = &v[..=3]; // out-of-bounds: upper bound == len
    }

    #[test]
    #[should_panic]
    fn inclusive_mut_upper_oob_panics() {
        let mut v: CopyStackVec<i32, 3> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        let _ = &mut v[..=3]; // out-of-bounds: upper bound == len
    }

    #[test]
    fn inclusive_single_element() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();
        v[1..=1].copy_from_slice(&[99]);
        assert_eq!(v.as_slice(), &[1, 99, 3]);
    }

    #[test]
    fn test_index_mut_single_element() {
        let mut v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2, 3, 4][..]).unwrap();

        // Mutate a single element via `IndexMut<usize>`.
        v[1] = 10;
        v[3] = 40;

        assert_eq!(v.as_slice(), &[1, 10, 3, 40]);
    }

    #[test]
    fn test_index_mut_range_from() {
        let mut v: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();

        {
            // `IndexMut<RangeFrom<usize>>` → &mut [T]
            let tail: &mut [i32] = &mut v[2..];
            tail.copy_from_slice(&[30, 40, 50]);
        }

        assert_eq!(v.as_slice(), &[1, 2, 30, 40, 50]);
    }

    #[test]
    fn test_index_mut_range_to() {
        let mut v: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();

        {
            // `IndexMut<RangeTo<usize>>` → &mut [T]
            let head: &mut [i32] = &mut v[..3];
            head.copy_from_slice(&[10, 20, 30]);
        }

        assert_eq!(v.as_slice(), &[10, 20, 30, 4, 5]);
    }

    #[test]
    fn test_index_mut_range_full() {
        let mut v: CopyStackVec<i32, 3> = CopyStackVec::try_from(&[1, 2, 3][..]).unwrap();

        {
            // `IndexMut<RangeFull>` → &mut [T]
            let all: &mut [i32] = &mut v[..];
            all.copy_from_slice(&[7, 8, 9]);
        }

        assert_eq!(v.as_slice(), &[7, 8, 9]);
    }
}
