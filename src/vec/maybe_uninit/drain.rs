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

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Drains the specified range of elements and returns them as an iterator.
    ///
    /// Elements in `range` are copied out into a temporary `CopyStackVec`
    /// and yielded by value. The remainder of the vector is shifted left.
    ///
    /// This matches the behavior of [`Vec::drain`].
    ///
    /// # Panics
    ///
    /// Panics if the specified range is invalid:
    /// - `start > end`
    /// - `end > self.len()`
    ///
    /// (A range with `start == end` yields an empty iterator and leaves
    /// the vector unchanged.)
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

#[cfg(test)]
mod tests {
    use crate::vec::CopyStackVec;
    #[test]
    fn test_drain_non_default_type_in_maybe_uninit_backend() {
        #[derive(Copy, Clone, Debug, PartialEq, Eq)]
        struct NoDefault(i32); // intentionally no Default

        let mut v: CopyStackVec<NoDefault, 5> = CopyStackVec::from_slice_truncated(&[
            NoDefault(1),
            NoDefault(2),
            NoDefault(3),
            NoDefault(4),
        ]);

        // Drain the middle two
        let drained: alloc::vec::Vec<_> = v.drain(1..3).collect();
        assert_eq!(drained, [NoDefault(2), NoDefault(3)]);

        // Remaining should be [1,4] in order
        assert_eq!(v.len(), 2);
        assert_eq!(v.as_slice(), &[NoDefault(1), NoDefault(4)]);
    }
}
