// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::{error::Error, vec::CopyStackVec};

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Converts to `[T; N]` when **full** (`len == N`), otherwise returns [`Error::InvalidLen`].
    #[inline]
    pub fn try_into_array(self) -> Result<[T; N], Error> {
        if self.len == N {
            Ok(self.buf)
        } else {
            Err(Error::InvalidLen)
        }
    }
}
