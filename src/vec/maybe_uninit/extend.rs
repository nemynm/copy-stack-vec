// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> Extend<T> for CopyStackVec<T, N> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let remaining = N - self.len;
        if remaining == 0 {
            return;
        }

        for item in iter.into_iter().take(remaining) {
            self.buf[self.len].write(item);
            self.len += 1;
        }
    }
}

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Extends from `src` if it fits; otherwise no-op and returns [`Error::Full`].
    #[inline]
    pub fn extend_from_slice(&mut self, src: &[T]) -> Result<(), crate::Error> {
        let avail = N - self.len;
        if src.len() > avail {
            return Err(crate::Error::Full);
        }
        let len = self.len;

        // Write elements into the uninitialized tail
        for (i, item) in src.iter().enumerate() {
            self.buf[len + i].write(*item);
        }

        self.len = len + src.len();
        Ok(())
    }

    /// Copies as many elements from `src` as will fit and returns the count copied.
    #[inline]
    pub fn extend_from_slice_truncated(&mut self, src: &[T]) -> usize {
        let len = self.len;
        let avail = N - len;
        let take = avail.min(src.len());

        for (i, item) in src.iter().take(take).enumerate() {
            self.buf[len + i].write(*item);
        }

        self.len = len + take;
        take
    }

    /// Tries to extend `self` from an iterator **without truncation**.
    ///
    /// Semantics:
    /// - All-or-nothing:
    ///   - If the iterator yields at most `spare_capacity()` items, they are
    ///     appended in order and `Ok(())` is returned.
    ///   - If it yields more than `spare_capacity()`, this returns
    ///     `Err(Error::Full)` and `self` is left unchanged.
    /// - The source iterator may be partially consumed on error.
    #[inline]
    pub fn try_extend_from_iter<I: IntoIterator<Item = T>>(
        &mut self,
        iter: I,
    ) -> Result<(), crate::Error> {
        let spare = N - self.len;

        // Temporary buffer to ensure `self` is unchanged on error.
        let mut tmp: CopyStackVec<T, N> = CopyStackVec::default();
        for item in iter {
            if tmp.len() == spare {
                return Err(crate::Error::Full);
            }
            tmp.push(item)?; // propagate Error::Full from tmp
        }

        let slice = tmp.as_slice();
        self.extend_from_slice(slice)
    }
}
