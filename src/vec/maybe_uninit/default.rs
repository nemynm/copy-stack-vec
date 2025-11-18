// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::vec::CopyStackVec;

// Core imports
use core::mem::MaybeUninit;

impl<T: Copy, const N: usize> Default for CopyStackVec<T, N> {
    fn default() -> Self {
        Self {
            buf: [MaybeUninit::<T>::uninit(); N],
            len: 0,
        }
    }
}
