// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        // SAFETY: By invariant, all elements in `buf[..self.len]` are initialized,
        // and `self.len <= N`, so this creates a valid shared slice of initialized `T`.
        unsafe { core::slice::from_raw_parts(self.buf.as_ptr() as *const T, self.len) }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: By invariant, all elements in `buf[..self.len]` are initialized,
        // and `self.len <= N`. We have exclusive access via `&mut self`, so it is
        // sound to create a mutable slice over `buf[..self.len]`.
        unsafe { core::slice::from_raw_parts_mut(self.buf.as_mut_ptr() as *mut T, self.len) }
    }

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
