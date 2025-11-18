// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> FromIterator<T> for CopyStackVec<T, N> {
    /// Collecting into CopyStackVec<T, N> takes at most the first N elements from the iterator and
    /// does not consume any further elements.
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut v = Self::default();
        v.extend(iter);
        v
    }
}
