// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy + Default, const N: usize> Default for CopyStackVec<T, N> {
    fn default() -> Self {
        Self {
            buf: [T::default(); N],
            len: 0,
        }
    }
}
