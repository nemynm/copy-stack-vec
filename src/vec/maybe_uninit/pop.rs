// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Pops the last element if any.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            // SAFETY: Before decrementing, all elements in `buf[..old_len]` are
            // initialized by invariant, so `buf[self.len]` (the old last slot)
            // still contains an initialized `T`.
            let out = unsafe { self.buf[self.len].assume_init() };
            Some(out)
        }
    }
}
