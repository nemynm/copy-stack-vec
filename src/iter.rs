// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Iterator support for [`CopyStackVec`](crate::CopyStackVec).
//!
//! - `IntoIter<T, N>` yields by value and supports `DoubleEndedIterator`,
//!   `ExactSizeIterator`, and `FusedIterator`.
//! - `&CopyStackVec` and `&mut CopyStackVec` iterate as slices.

#[cfg(not(feature = "unsafe-maybe-uninit"))]
mod array;
#[cfg(feature = "unsafe-maybe-uninit")]
mod maybe_uninit;

// Crate imports
use crate::vec::CopyStackVec;

// Core imports
use core::iter::FusedIterator;

/// Owned iterator returned by `CopyStackVec::into_iter()`.
///
/// Yields elements by value from front to back and supports double-ended
/// iteration via [`DoubleEndedIterator`].
pub struct IntoIter<T: Copy, const N: usize> {
    pub(crate) v: CopyStackVec<T, N>,
    pub(crate) front: usize,
    pub(crate) back: usize, // exclusive
}

impl<T: Copy, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.front < self.back {
            let i = self.front;
            self.front += 1;
            Some(self.v.as_slice()[i])
        } else {
            None
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.back - self.front;
        (rem, Some(rem))
    }
    fn nth(&mut self, n: usize) -> Option<T> {
        let rem = self.back - self.front;
        if n >= rem {
            self.front = self.back;
            return None;
        }
        let i = self.front + n; // safe: n < rem == back - front
        self.front = i + 1;
        Some(self.v.as_slice()[i])
    }
}

impl<T: Copy, const N: usize> DoubleEndedIterator for IntoIter<T, N> {
    fn next_back(&mut self) -> Option<T> {
        if self.front < self.back {
            self.back -= 1;
            Some(self.v.as_slice()[self.back])
        } else {
            None
        }
    }
    fn nth_back(&mut self, n: usize) -> Option<T> {
        let rem = self.back - self.front;
        if n >= rem {
            self.front = self.back;
            None
        } else {
            self.back -= n + 1;
            Some(self.v.as_slice()[self.back])
        }
    }
}
impl<T: Copy, const N: usize> FusedIterator for IntoIter<T, N> {}
impl<T: Copy, const N: usize> ExactSizeIterator for IntoIter<T, N> {}

impl<'a, T: Copy, const N: usize> IntoIterator for &'a CopyStackVec<T, N> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}
impl<'a, T: Copy, const N: usize> IntoIterator for &'a mut CopyStackVec<T, N> {
    type Item = &'a mut T;
    type IntoIter = core::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.as_mut_slice().iter_mut()
    }
}
impl<T: Copy, const N: usize> IntoIterator for CopyStackVec<T, N> {
    type Item = T;
    type IntoIter = IntoIter<T, N>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            front: 0,
            back: self.len,
            v: self,
        }
    }
}

#[cfg(test)]
mod tests {
    // Imports
    use super::CopyStackVec;

    #[test]
    fn test_double_ended_and_nth() {
        let v: CopyStackVec<i32, 6> = CopyStackVec::try_from(&[10, 20, 30, 40][..]).unwrap();
        let mut it = v.into_iter();
        assert_eq!(it.next(), Some(10));
        assert_eq!(it.next_back(), Some(40));
        assert_eq!(it.nth(1), Some(30));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_into_iter_nth_back_sequence() {
        let v: CopyStackVec<i32, 6> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();
        let mut it = v.into_iter();
        assert_eq!(it.nth_back(0), Some(5));
        assert_eq!(it.nth_back(1), Some(3)); // skip 1 from back, take 3
        assert_eq!(it.next_back(), Some(2));
        assert_eq!(it.next(), Some(1));
        assert_eq!(it.next(), None);
    }

    #[test]
    #[allow(clippy::iter_nth_zero)]
    fn test_size_hint_tracks_consumption() {
        let v: CopyStackVec<i32, 6> = CopyStackVec::try_from(&[10, 20, 30, 40][..]).unwrap();
        let mut it = v.into_iter();
        assert_eq!(it.size_hint(), (4, Some(4)));
        assert_eq!(it.next(), Some(10));
        assert_eq!(it.size_hint(), (3, Some(3)));
        assert_eq!(it.next_back(), Some(40));
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert_eq!(it.nth(0), Some(20));
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next(), Some(30));
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
    }

    #[test]
    #[allow(clippy::iter_nth_zero)]
    fn test_nth_and_nth_back_boundary_conditions() {
        let v: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();
        let mut it = v.into_iter();

        // nth exactly remaining-1 returns last; nth >= remaining drains
        assert_eq!(it.nth(3), Some(4)); // consumed [1,2,3], returns 4, remaining [5]
        assert_eq!(it.nth(0), Some(5));
        assert_eq!(it.nth(0), None);

        let v2: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[1, 2, 3, 4, 5][..]).unwrap();
        let mut it2 = v2.into_iter();
        assert_eq!(it2.nth_back(4), Some(1)); // exactly remaining-1 from back
        assert_eq!(it2.next(), None);
    }

    #[test]
    fn test_into_iter_zero_sized_type() {
        let v: CopyStackVec<(), 3> = CopyStackVec::from([(); 3]);
        let it = v.into_iter();
        assert_eq!(it.size_hint(), (3, Some(3)));
        assert_eq!(it.count(), 3);
    }

    #[test]
    fn test_into_iter_zero_capacity() {
        let v: CopyStackVec<u8, 0> = CopyStackVec::default();
        let mut it = v.into_iter();
        assert_eq!(it.next(), None);
        assert_eq!(it.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_nth_back_overflow_branch() {
        let v: CopyStackVec<i32, 5> = CopyStackVec::try_from(&[10, 20, 30][..]).unwrap();
        let mut it = v.into_iter();

        // remaining = 3; n >= 3 → n = 3 or more will trigger overflow branch
        assert_eq!(it.nth_back(3), None);

        // Iterator must now be fully drained
        assert_eq!(it.next(), None);
        assert_eq!(it.next_back(), None);

        // size_hint must be zero after draining
        assert_eq!(it.size_hint(), (0, Some(0)));
    }

    #[test]
    fn test_nth_back_exactly_remaining_branch() {
        let v: CopyStackVec<i32, 4> = CopyStackVec::try_from(&[1, 2][..]).unwrap();
        let mut it = v.into_iter();

        // remaining = 2, so nth_back(2) should hit the n >= rem branch
        assert_eq!(it.nth_back(2), None);

        // fully drained
        assert_eq!(it.next(), None);
        assert_eq!(it.next_back(), None);
    }
}
