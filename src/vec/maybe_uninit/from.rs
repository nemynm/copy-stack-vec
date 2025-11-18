// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate import
use crate::vec::CopyStackVec;

// Core imports
use core::mem::MaybeUninit;

impl<T: Copy, const N: usize> From<[T; N]> for CopyStackVec<T, N> {
    fn from(src: [T; N]) -> Self {
        let mut buf: [MaybeUninit<T>; N] = [MaybeUninit::uninit(); N];
        for (i, v) in src.into_iter().enumerate() {
            buf[i].write(v);
        }

        Self { buf, len: N }
    }
}

impl<T: Copy, const N: usize> From<&[T; N]> for CopyStackVec<T, N> {
    fn from(src: &[T; N]) -> Self {
        // Reuse the owned-array impl by copying the array.
        // For Copy types this is just a by-value copy of `[T; N]`.
        (*src).into()
    }
}
