// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::{error::Error, vec::CopyStackVec};

impl<T: Copy, const N: usize> TryFrom<&[T]> for CopyStackVec<T, N> {
    type Error = Error;
    fn try_from(src: &[T]) -> Result<Self, Error> {
        let mut v = Self::default();
        v.extend_from_slice(src)?;
        Ok(v)
    }
}
