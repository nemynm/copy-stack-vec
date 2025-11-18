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
            // Take a copy of the value at `read`.
            let v = unsafe {
                // SAFETY: `read < self.len`, so `buf[read]` is within the
                // initialized prefix and contains a valid `T`.
                self.buf[read].assume_init()
            };
            if f(&v) {
                if write != read {
                    self.buf[write].write(v);
                }
                write += 1;
            }
            // We do not handle the old contents at `read`; after we
            // shrink len, positions >= write are logically uninitialized.
        }
        self.len = write;
    }
}
