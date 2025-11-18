// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy + Default, const N: usize> CopyStackVec<T, N> {
    /// Constructs an empty vector with all elements initialized to `Default::default()`.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Constructs an empty vector with the backing buffer filled with `fill`.
    ///
    /// Note: the initial **length** is `0`. The filled values become visible
    /// only as you push/resize.
    #[inline]
    pub const fn new_with(fill: T) -> Self {
        Self {
            buf: [fill; N],
            len: 0,
        }
    }
}
