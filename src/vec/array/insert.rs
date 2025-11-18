// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::{error::Error, vec::CopyStackVec};

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Inserts `value` at `index`, shifting elements to the right.
    ///
    /// - Returns [`Error::OutOfBounds`] if `index > len`.
    /// - Returns [`Error::Full`] if at capacity.
    ///
    /// Uses `copy_within` for overlap-safe shifting.
    #[inline]
    pub fn insert(&mut self, index: usize, value: T) -> Result<(), Error> {
        if index > self.len {
            return Err(Error::OutOfBounds);
        }
        if self.len == N {
            return Err(Error::Full);
        }
        let len = self.len;

        // Shift right: [index..len) -> [index+1..len+1)
        self.buf.copy_within(index..len, index + 1);
        self.buf[index] = value;

        self.len = len + 1;
        Ok(())
    }
}
