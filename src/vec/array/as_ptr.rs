// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Returns a raw pointer to the start of the backing storage.
    ///
    /// The entire backing array is initialized, but only the first `len` elements
    /// are logically part of the vector.
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self.buf.as_ptr()
    }

    /// Returns a mutable raw pointer to the start of the backing storage.
    ///
    /// The entire backing array is initialized, but only the first `len` elements
    /// are logically part of the vector. Writes beyond `len` do not change the
    /// vector's logical length.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.buf.as_mut_ptr()
    }
}
