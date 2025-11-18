// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Returns a raw pointer to the start of the backing storage.
    ///
    /// Only the first `len` elements are logically initialized as `T`. Code that
    /// dereferences this pointer must:
    ///
    /// - treat `self.len` as the number of initialized elements, and
    /// - avoid reading from `ptr.add(i)` for any `i >= self.len`.
    ///
    /// Writing to the memory beyond `len` is allowed from Rust’s point of view,
    /// but it does **not** update `len`, and such writes will not be reflected in
    /// the logical contents of the `CopyStackVec`.
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self.buf.as_ptr() as *const T
    }

    /// Returns a mutable raw pointer to the start of the backing storage.
    ///
    /// Only the first `len` elements are logically initialized as `T`. Code that
    /// dereferences this pointer must:
    ///
    /// - treat `self.len` as the number of initialized elements, and
    /// - avoid reading from `ptr.add(i)` for any `i >= self.len`.
    ///
    /// Writing to the memory beyond `len` is allowed from Rust’s point of view,
    /// but it does **not** update `len`, and such writes will not be reflected in
    /// the logical contents of the `CopyStackVec`.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.buf.as_mut_ptr() as *mut T
    }
}
