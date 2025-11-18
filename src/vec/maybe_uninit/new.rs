// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Constructs an empty vector.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Constructs an empty vector with the backing buffer filled with `fill`.
    ///
    /// Note: the initial **length** is `0`. The filled values become visible
    /// only as you push/resize.
    pub fn new_with(fill: T) -> Self {
        use core::mem::MaybeUninit;
        Self {
            buf: [MaybeUninit::new(fill); N],
            len: 0,
        }
    }
}
