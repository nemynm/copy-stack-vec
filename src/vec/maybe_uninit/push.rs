// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::{error::Error, vec::CopyStackVec};

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Pushes `v` if not full; returns [`Error::Full`] otherwise.
    #[inline]
    pub fn push(&mut self, v: T) -> Result<(), Error> {
        if self.len == N {
            return Err(Error::Full);
        }

        self.buf[self.len].write(v);

        self.len += 1;
        Ok(())
    }

    /// Pushes `v` if not full; if at capacity, no-op and returns `false`.
    #[inline]
    #[must_use]
    pub fn push_truncated(&mut self, v: T) -> bool {
        if self.len == N {
            return false;
        }
        self.buf[self.len].write(v);
        self.len += 1;
        true
    }
}
