// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy + Default, const N: usize> CopyStackVec<T, N> {
    /// Tries to construct from an iterator, erroring with [`Error::Full`] if it would overflow.
    ///
    /// Semantics:
    /// - Elements are pushed in iterator order.
    /// - On the first element that would exceed capacity `N`, this returns `Err(Error::Full)`.
    /// - Any elements pushed before the overflow are discarded; the returned `Err` does *not*
    ///   include the partially filled vector.
    /// - The source iterator may be left partially consumed (it stops at the first overflow).
    #[inline]
    pub fn try_from_iter<I: IntoIterator<Item = T>>(iter: I) -> Result<Self, crate::Error> {
        let mut v = Self::default();
        for item in iter {
            v.push(item)?; // returns Err(Full) on overflow → we bail out immediately
        }
        Ok(v)
    }
}
