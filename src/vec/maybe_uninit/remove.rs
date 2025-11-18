// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Removes and returns the element at `index`, shifting subsequent elements left.
    ///
    /// Returns `None` if `index >= len`. Uses `copy_within` for overlap-safe shifting.
    #[inline]
    pub fn remove(&mut self, index: usize) -> Option<T> {
        if index >= self.len {
            return None;
        }
        let len = self.len;

        // Read the element at `index` as a `T`.
        let out = unsafe {
            // SAFETY: `index < self.len`, so `buf[index]` is within the initialized
            // prefix `buf[..len]` by invariant and contains a valid `T`.
            self.buf[index].assume_init()
        };

        // Shift left: [index+1..len) -> [index..len-1)
        if index + 1 < len {
            self.buf.copy_within(index + 1..len, index);
        }

        self.len = len - 1;
        Some(out)
    }

    /// Removes and returns the element at `index` by swapping with the last element.
    ///
    /// Preserves neither order nor contiguity of the last two elements. Returns `None`
    /// when `index >= len`. Removing the last element avoids a swap.
    #[inline]
    pub fn swap_remove(&mut self, index: usize) -> Option<T> {
        if index >= self.len {
            return None;
        }
        self.len -= 1;
        let last = self.len;

        // Read out the element at `index` as a `T`.
        let out = unsafe {
            // SAFETY: Before decrement, `index < old_len`, so `buf[index]` is
            // within the initialized prefix and contains a valid `T`.
            self.buf[index].assume_init()
        };

        // If it's not the last element, move the last slot into the hole.
        if index != last {
            self.buf[index] = self.buf[last];
        }

        Some(out)
    }
}
