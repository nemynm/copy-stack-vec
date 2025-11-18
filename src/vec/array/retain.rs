// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate import
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Retains only the elements specified by the predicate `f`, preserving order.
    ///
    /// The predicate is applied to each element in iteration order.
    #[inline]
    pub fn retain<F: FnMut(&T) -> bool>(&mut self, mut f: F) {
        let mut write = 0;
        for read in 0..self.len {
            if f(&self.buf[read]) {
                if write != read {
                    self.buf[write] = self.buf[read];
                }
                write += 1;
            }
        }
        self.len = write;
    }
}
