// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::{error::Error, vec::CopyStackVec};

impl<T: Copy + Default, const N: usize> CopyStackVec<T, N> {
    /// Splits the vector into two at index `at`.
    ///
    /// On success:
    /// - `self` is left containing the prefix `[0..at)`,
    /// - the returned vector contains the tail `[at..len)`.
    ///
    /// Returns [`Error::OutOfBounds`] if `at > self.len()`. On error, `self`
    /// is left unchanged.
    #[inline]
    pub fn split_off(&mut self, at: usize) -> Result<Self, Error> {
        let len = self.len;
        if at > len {
            return Err(Error::OutOfBounds);
        }

        let tail_len = len - at;
        let mut other: CopyStackVec<T, N> = CopyStackVec::default();

        if tail_len > 0 {
            // This must fit by construction: tail_len <= len <= N and other is empty.
            // We still propagate any error instead of panicking.
            other.extend_from_slice(&self.as_slice()[at..len])?;
        }

        // Shrink self to the prefix.
        self.len = at;

        Ok(other)
    }
}
