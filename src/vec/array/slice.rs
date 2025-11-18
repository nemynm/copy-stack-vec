// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Returns the initialized prefix as a shared slice (`&self.buf[..len]`).
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        &self.buf[..self.len]
    }

    /// Returns the initialized prefix as a mutable slice (`&mut self.buf[..len]`).
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        let len = self.len;
        &mut self.buf[..len]
    }
}

impl<T: Copy + Default, const N: usize> CopyStackVec<T, N> {
    /// Constructs from at most `N` elements of `src`, truncating if necessary.
    #[inline]
    pub fn from_slice_truncated(src: &[T]) -> Self {
        let mut v = Self::default();
        let _ = v.extend_from_slice_truncated(src);
        v
    }

    /// Constructs from at most `N` elements of `src`, truncating if necessary.
    ///
    /// Convenience wrapper over [`from_slice_truncated`] for arrays.
    #[inline]
    pub fn from_array_truncated<const M: usize>(src: &[T; M]) -> Self {
        Self::from_slice_truncated(&src[..])
    }
}
