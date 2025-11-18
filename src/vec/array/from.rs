// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

impl<T: Copy, const N: usize> From<[T; N]> for CopyStackVec<T, N> {
    fn from(buf: [T; N]) -> Self {
        Self { buf, len: N }
    }
}

impl<T: Copy, const N: usize> From<&[T; N]> for CopyStackVec<T, N> {
    fn from(src: &[T; N]) -> Self {
        (*src).into()
    }
}
