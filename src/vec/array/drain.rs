// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::{iter::IntoIter, vec::CopyStackVec};

// Core imports
use core::{
    iter::FusedIterator,
    ops::{Bound, RangeBounds},
};

/// Owned iterator returned by `CopyStackVec::drain`.
///
/// - Holds a mutable borrow of the parent vector for the iterator's lifetime.
/// - Internally just wraps an `IntoIter` over a temporary `CopyStackVec`
///   containing the drained elements.
pub struct Drain<'a, T: Copy, const N: usize> {
    pub(crate) _parent: &'a mut CopyStackVec<T, N>,
    pub(crate) iter: IntoIter<T, N>,
}

impl<'a, T: Copy, const N: usize> Iterator for Drain<'a, T, N> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn nth(&mut self, n: usize) -> Option<T> {
        self.iter.nth(n)
    }
}

impl<'a, T: Copy, const N: usize> DoubleEndedIterator for Drain<'a, T, N> {
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back()
    }

    fn nth_back(&mut self, n: usize) -> Option<T> {
        self.iter.nth_back(n)
    }
}

impl<'a, T: Copy, const N: usize> ExactSizeIterator for Drain<'a, T, N> {}
impl<'a, T: Copy, const N: usize> FusedIterator for Drain<'a, T, N> {}

impl<T: Copy + Default, const N: usize> CopyStackVec<T, N> {
    /// Drains the specified range of elements and returns them as an iterator.
    ///
    /// The elements in `range` are removed immediately and yielded by value.
    /// The tail of the vector is shifted left to fill the gap.
    ///
    /// This follows the same semantics as [`Vec::drain`]:
    ///
    /// # Panics
    ///
    /// Panics if the range is invalid:
    /// - `start > end`
    /// - `end > self.len()`
    ///
    /// (Note: `start == end` is allowed and produces an empty iterator.)
    ///
    /// # Examples
    /// ```
    /// # use copy_stack_vec::CopyStackVec;
    /// let mut v: CopyStackVec<_, 4> = [1, 2, 3, 4].into();
    /// let drained: CopyStackVec<_, 4> = v.drain(1..3).collect();
    /// assert_eq!(drained.as_slice(), &[2, 3]);
    /// assert_eq!(v.as_slice(), &[1, 4]);
    /// ```
    pub fn drain<R>(
        &mut self,
        range: R,
    ) -> impl DoubleEndedIterator<Item = T> + ExactSizeIterator + FusedIterator + '_
    where
        R: RangeBounds<usize>,
    {
        let len = self.len();

        let start = match range.start_bound() {
            Bound::Included(&i) => i,
            Bound::Excluded(&i) => i + 1,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(&i) => i + 1,
            Bound::Excluded(&i) => i,
            Bound::Unbounded => len,
        };

        if start > end {
            panic!("drain range start > end: {} > {}", start, end);
        }
        if end > len {
            panic!("drain range end {} exceeds length {}", end, len);
        }

        if start == end {
            // Empty drain
            let tmp: CopyStackVec<T, N> = CopyStackVec::default();
            return Drain {
                _parent: self,
                iter: tmp.into_iter(),
            };
        }

        // Copy drained items into temporary vec
        let slice = &self.as_slice()[start..end];
        let mut tmp: CopyStackVec<T, N> = CopyStackVec::default();
        tmp.extend_from_slice(slice).unwrap();

        // Shift tail left
        let range_len = end - start;
        let tail_len = len - end;
        if tail_len > 0 {
            self.as_mut_slice().copy_within(end..len, start);
        }
        self.len = len - range_len;

        Drain {
            _parent: self,
            iter: tmp.into_iter(),
        }
    }
}
