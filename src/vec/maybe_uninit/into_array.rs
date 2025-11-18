// This file is part of copy-stack-vec.
// SPDX-License-Identifier: MIT OR Apache-2.0

// Crate imports
use crate::{CopyStackVec, Error};

impl<T: Copy, const N: usize> CopyStackVec<T, N> {
    /// Converts to `[T; N]` when **full** (`len == N`), otherwise returns [`Error::InvalidLen`].
    ///
    /// In the `unsafe-maybe-uninit` backend, the backing storage is
    /// `[MaybeUninit<T>; N]`. This consumes the buffer and builds a `[T; N]`
    /// element-wise.
    #[inline]
    pub fn try_into_array(self) -> Result<[T; N], Error> {
        use core::mem::MaybeUninit;

        if self.len != N {
            return Err(Error::InvalidLen);
        }

        let buf = self.buf; // [MaybeUninit<T>; N]

        // Create uninitialized [T; N]
        let mut out: MaybeUninit<[T; N]> = MaybeUninit::uninit();
        let out_ptr = out.as_mut_ptr() as *mut T;

        for (i, elem) in buf.into_iter().enumerate() {
            unsafe {
                // SAFETY: `self.len == N` and by invariant all `buf[..N]` are
                // initialized, so `elem.assume_init()` yields a valid `T`. We
                // write exactly N such values into `out_ptr[..N]`.
                out_ptr.add(i).write(elem.assume_init());
            }
        }

        Ok(unsafe {
            // SAFETY: The loop above wrote N initialized `T` values into `out`, so it
            // now contains a fully-initialized `[T; N]`.
            out.assume_init()
        })
    }
}
