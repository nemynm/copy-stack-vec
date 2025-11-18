// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::{error::Error, vec::CopyStackVec};

impl<T: Copy, const N: usize> Extend<T> for CopyStackVec<T, N> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let remaining = N - self.len;
        if remaining == 0 {
            return;
        }

        for item in iter.into_iter().take(remaining) {
            self.buf[self.len] = item;
            self.len += 1;
        }
    }
}

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Extends from `src` if it fits; otherwise no-op and returns [`Error::Full`].
    #[inline]
    pub fn extend_from_slice(&mut self, src: &[T]) -> Result<(), Error> {
        let avail = N - self.len;
        if src.len() > avail {
            return Err(Error::Full);
        }
        let len = self.len;
        self.buf[len..len + src.len()].copy_from_slice(src);
        self.len = len + src.len();
        Ok(())
    }

    /// Copies as many elements from `src` as will fit and returns the count copied.
    #[inline]
    #[must_use]
    pub fn extend_from_slice_truncated(&mut self, src: &[T]) -> usize {
        let len = self.len;
        let avail = N - len;
        let take = avail.min(src.len());
        self.buf[len..len + take].copy_from_slice(&src[..take]);
        self.len = len + take;
        take
    }
}

impl<T: Copy + Default, const N: usize> CopyStackVec<T, N> {
    /// Tries to extend `self` from an iterator **without truncation**.
    ///
    /// Semantics:
    /// - All-or-nothing:
    ///   - If the iterator yields at most `spare_capacity()` items, they are
    ///     appended in order and `Ok(())` is returned.
    ///   - If it yields more than `spare_capacity()`, this returns `Err(Error::Full)`
    ///     and `self` is left unchanged.
    /// - The source iterator may be partially consumed on error; no elements
    ///   are written into `self` unless the whole extend succeeds.
    #[inline]
    pub fn try_extend_from_iter<I: IntoIterator<Item = T>>(
        &mut self,
        iter: I,
    ) -> Result<(), Error> {
        let spare = N - self.len;

        // Temporary buffer to ensure `self` is unchanged on error.
        let mut tmp: CopyStackVec<T, N> = CopyStackVec::default();
        for item in iter {
            if tmp.len() == spare {
                return Err(Error::Full);
            }
            // tmp.len() < spare <= N so this cannot overflow tmp; but if it ever
            // did, we just propagate the error instead of panicking.
            tmp.push(item)?;
        }

        // Now we know everything fits into `self`.
        self.extend_from_slice(tmp.as_slice())
    }
}
