// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::{CopyStackVec, Error};

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
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
            let slice = &self.as_slice()[at..len];
            other.extend_from_slice(slice)?; // propagate instead of panicking
        }

        self.len = at;

        Ok(other)
    }
}
